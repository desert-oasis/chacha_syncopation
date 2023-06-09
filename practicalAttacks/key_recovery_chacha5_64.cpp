#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <random>
#include <cassert>
#include <fstream>
#include <sys/time.h>
#include "chacha.cpp"


using namespace std;

//FUNCTIONS
#define GET_BIT(a,p) (((a)>>(p))&0x1)


/*Random number generator*/
mt19937 gen((unsigned int) time(NULL)); //seed random generator every time


/*MISCS*/
void GetRandomUint32(uint32_t *r,int lenWords){
	for(int i=0;i<lenWords;i++) r[i]=gen();
}


double CorrelationFormula(uint64_t occurrence,uint64_t NS){
	return 2.0*((double)occurrence/(double)NS)-1.0;
}


//Attack parameters
const int numCipher=(int)5.0;
const int numDiff=ceil(2.5);

//Forward distinguisher
int ID_indexWord=1;
int ID_indexBit=6;
int OD_indexWord=2;
int OD_indexBit=0;
//Backward computation
int numKeyBitsGuessed=8;
int numConds=4; //with syncopation
//Data complexity
uint64_t N_star=pow(2,6.4);
uint64_t N_total=N_star*(1<<(2*numConds));
uint64_t M=N_star*(1<<numConds);

int flagDebug=0;


int GetValue_SR(const uint32_t Z[16]){
	int res=0;

	res+=GET_BIT(Z[4],6);
	res+=GET_BIT(Z[4],9) << 1;
	res+=GET_BIT(Z[4],18) << 2;
	res+=GET_BIT(Z[5],6) << 3;

	return res;
}
void GenerateDataIO(const uint32_t key[8], uint32_t **dataIO, uint64_t *numData_filtered){
	assert(ID_indexWord==1);
	for(uint64_t i_data=0;i_data<N_total;i_data++){
		ECRYPT_ctx X0,X1;
		ECRYPT_keysetup32(&X0,key);
		ECRYPT_keysetup32(&X1,key);
		uint32_t iv0[4],iv1[4];
		GetRandomUint32(iv0,4);
		iv1[0]=iv0[0];
		iv1[2]=iv0[2];
		iv1[3]=iv0[3];
		iv1[1]=iv0[1]^((uint32_t)1<<ID_indexBit);//assert(ID_indexWord==1);
		ECRYPT_ivsetup32(&X0,iv0);
		ECRYPT_ivsetup32(&X1,iv1);
		//compute keystream Z0 and Z1
		uint32_t Z0[16],Z1[16];
		chacha_block_reduced(Z0,X0.input,numCipher);
		chacha_block_reduced(Z1,X1.input,numCipher);

		//STEP1: Pre-process data, classify pairs into subsets according to the values of S^R
		int value_SR_Z0,value_SR_Z1; 
		value_SR_Z0=GetValue_SR(Z0);
		value_SR_Z1=GetValue_SR(Z1);
		if(value_SR_Z0==value_SR_Z1){
			if(numData_filtered[value_SR_Z0]<N_star){
				uint64_t tmpIndex=value_SR_Z0*N_star+numData_filtered[value_SR_Z0];
				int i;
				for(i=0;i<4;i++) dataIO[tmpIndex][i]=iv0[i];
				for(i=0;i<16;i++) dataIO[tmpIndex][4+i]=Z0[i];
				for(i=0;i<16;i++) dataIO[tmpIndex][20+i]=Z1[i];
				numData_filtered[value_SR_Z0]++;
			}
		}
	}
}

int GetValue_kR(const int valueKeyBits){
	int res=0;

	//8 restricted key bits: {6, 9, 18, 38}, from LSB to MSB
	res+=GET_BIT(valueKeyBits,0);
	res+=GET_BIT(valueKeyBits,1) << 1;
	res+=GET_BIT(valueKeyBits,6) << 2;
	res+=GET_BIT(valueKeyBits,7) << 3;

	return res;
}
void AssignInitS(ECRYPT_ctx *pX,const uint32_t *subk,const int valueKeyBits,const int numKeyBits){
	assert(numKeyBits==8);

	pX->input[0] = 0x61707865;
	pX->input[1] = 0x3320646e;
	pX->input[2] = 0x79622d32;
	pX->input[3] = 0x6b206574;

	for(int i=0;i<6;i++) pX->input[6+i]=subk[i];

	pX->input[4]=0;
	pX->input[5]=0;
	//8 guessed key bits: {6, 9, 10, 11, 12, 13, 18, 38}, from LSB to MSB
	pX->input[4]^=GET_BIT(valueKeyBits,0) << 6;
	pX->input[4]^=GET_BIT(valueKeyBits,1) << 9;
	pX->input[4]^=GET_BIT(valueKeyBits,2) << 10;
	pX->input[4]^=GET_BIT(valueKeyBits,3) << 11;
	pX->input[4]^=GET_BIT(valueKeyBits,4) << 12;
	pX->input[4]^=GET_BIT(valueKeyBits,5) << 13;
	pX->input[4]^=GET_BIT(valueKeyBits,6) << 18;
	pX->input[5]^=GET_BIT(valueKeyBits,7) << 6;
}
int ProcedureKeyRecovery_ChaCha5(const uint32_t *subkey_known, uint32_t **dataIO, uint64_t *numData_filtered){
	//STEP2: Exhaustively search all the guessed key bits, and recover them
	double cor_max=0.0; int iK_guessed_max=-1;//denote no value of guessed key with non-zero correlation
	double cor[1<<numKeyBitsGuessed];
	for(int iK_guessed=0;iK_guessed<(1<<numKeyBitsGuessed);iK_guessed++){
		//first, according to k^R, choose subsets in which element's values of S^R satisfying conditions
		int value_kR;
		value_kR=GetValue_kR(iK_guessed);
		int value_SR_Z=value_kR^0xf;//assert(numConds==4);
		/*Assign initial state:
			set the value of 8 guessed key bits and 
			fix the key bits in PNBs into zeros in X0 and X1.*/
		ECRYPT_ctx X0,X1;
		AssignInitS(&X0,subkey_known,iK_guessed,numKeyBitsGuessed);
		AssignInitS(&X1,subkey_known,iK_guessed,numKeyBitsGuessed);

		//then, compute the correlation at OD with filtered data
		uint64_t ctr=0;
		int NIV_filtered=numData_filtered[value_SR_Z];
		for(uint64_t iIV=0;iIV<NIV_filtered;iIV++){
			//obtain IV
			uint32_t iv0[4],iv1[4];
			int i;
			for(i=0;i<4;i++) iv0[i]=dataIO[value_SR_Z*N_star+iIV][i];
			iv1[1]=iv0[1]^((uint32_t)1<<ID_indexBit);//assert(ID_indexWord==1);
			iv1[0]=iv0[0];
			iv1[2]=iv0[2];
			iv1[3]=iv0[3];
			ECRYPT_ivsetup32(&X0,iv0);
			ECRYPT_ivsetup32(&X1,iv1);

			//backward compuation
			uint32_t X0_end[16],X0_mid[16];
			uint32_t X1_end[16],X1_mid[16];
			for(i=0;i<16;i++){
				X0_end[i]=dataIO[value_SR_Z*N_star+iIV][4+i]-X0.input[i];
				X1_end[i]=dataIO[value_SR_Z*N_star+iIV][20+i]-X1.input[i];
			}
			chacha_invRounds_reduced_half(X0_mid,X0_end,numCipher,numDiff);
			chacha_invRounds_reduced_half(X1_mid,X1_end,numCipher,numDiff);
			if(GET_BIT(X0_mid[OD_indexWord],OD_indexBit)==GET_BIT(X1_mid[OD_indexWord],OD_indexBit)) ctr++;
		}
		cor[iK_guessed]=CorrelationFormula(ctr,NIV_filtered);
		if(fabs(cor[iK_guessed])>cor_max){
			cor_max=fabs(cor[iK_guessed]);
			iK_guessed_max=iK_guessed;
		}

		// if(flagDebug==1) printf("when iK_guessed = %d, correlation is %.4f\n", iK_guessed,cor[iK_guessed]);
	}
	
	// if(flagDebug==1) printf("maximum of correlation is %.4f, when iK_guessed = %d\n", cor_max,iK_guessed_max);
	
	return iK_guessed_max;
}

void PraticalAttack_ChaCha5_withSyncopation(){
	int numK=10000;
	int ctrSucc=0;

	printf("###################################### BEGIN #######################################\n\n");
	int iK;
	for(iK=0;iK<numK;iK++){
		//Secret key
		uint32_t key[8];
		GetRandomUint32(key,8);
		uint32_t subkey_known[6];
		for(int i=0;i<6;i++) subkey_known[i]=key[2+i];


		// printf("############################# GENERATING DATA ######################################\n");
		// printf("...\n\n");
		//Array for storing data of input and output.
		uint32_t **dataIO=new uint32_t *[M];
		for(uint64_t i_data=0;i_data<M;i_data++) dataIO[i_data]=new uint32_t[4+2*16]; //(IV,Z0,Z1)
		uint64_t numData_filtered[1<<numConds];
		for(int i=0;i<(1<<numConds);i++) numData_filtered[i]=0;
		GenerateDataIO(key,dataIO,numData_filtered);
		// printf("###################################################################################\n\n");
		
		
		// printf("########################### ATTACK PROCEDURE: RECOVER KEY ########################\n");
		// printf("...\n\n");
		int valueK_max=ProcedureKeyRecovery_ChaCha5(subkey_known,dataIO,numData_filtered);
		assert(valueK_max>=0);
		// printf("################################################################################\n\n");

		for(uint64_t i_data=0;i_data<M;i_data++) delete[] dataIO[i_data];
		delete[] dataIO;

		int valueKey=0;
		valueKey+=GET_BIT(key[0],6);
		valueKey+=GET_BIT(key[0],9) << 1;
		valueKey+=GET_BIT(key[0],10) << 2;
		valueKey+=GET_BIT(key[0],11) << 3;
		valueKey+=GET_BIT(key[0],12) << 4;
		valueKey+=GET_BIT(key[0],13) << 5;
		valueKey+=GET_BIT(key[0],18) << 6;
		valueKey+=GET_BIT(key[1],6) << 7;
		if(flagDebug==1) printf("True value of 8 guessed key bits is %d.\n",valueKey);
		if(flagDebug==1) printf("Guessed value with maximum correlation is %d.\n", valueK_max);
		if(valueK_max==valueKey) {
			if(flagDebug==1) printf("Successfully recover 8 guessed key bits!\n\n");
			ctrSucc+=1;
		}
		else if(flagDebug==1) printf("Failed to recover the key bits!\n\n");
	}

	printf("There are %d out of %d random keys are successfully recovered 8 guessed key bits.\n",ctrSucc,numK);
	printf("###################################### END #######################################\n\n");
}

void PraticalAttack_ChaCha5_withoutSyncopation(){
	int numK=100;
	int ctrSucc=0;

	N_star=pow(2,21.1);
	N_total=N_star;
	printf("###################################### BEGIN #######################################\n\n");
	int iK;
	for(iK=0;iK<numK;iK++){
		//Secret key
		uint32_t key[8];
		GetRandomUint32(key,8);
		uint32_t subkey_known[6];
		for(int i=0;i<6;i++) subkey_known[i]=key[2+i];


		// printf("############################# GENERATING DATA ######################################\n");
		// printf("...\n\n");
		//Array for storing data of input and output.
		uint32_t **dataIO=new uint32_t *[N_total];
		uint64_t i_data;
		for(i_data=0;i_data<N_total;i_data++) dataIO[i_data]=new uint32_t[4+2*16]; //(IV,Z0,Z1)
		assert(ID_indexWord==1);
		for(i_data=0;i_data<N_total;i_data++){
			ECRYPT_ctx X0,X1;
			ECRYPT_keysetup32(&X0,key);
			ECRYPT_keysetup32(&X1,key);
			uint32_t iv0[4],iv1[4];
			GetRandomUint32(iv0,4);
			iv1[0]=iv0[0];
			iv1[2]=iv0[2];
			iv1[3]=iv0[3];
			iv1[1]=iv0[1]^((uint32_t)1<<ID_indexBit);//assert(ID_indexWord==1);
			ECRYPT_ivsetup32(&X0,iv0);
			ECRYPT_ivsetup32(&X1,iv1);
			//compute keystream Z0 and Z1
			uint32_t Z0[16],Z1[16];
			chacha_block_reduced(Z0,X0.input,numCipher);
			chacha_block_reduced(Z1,X1.input,numCipher);

			int i;
			for(i=0;i<4;i++) dataIO[i_data][i]=iv0[i];
			for(i=0;i<16;i++) dataIO[i_data][4+i]=Z0[i];
			for(i=0;i<16;i++) dataIO[i_data][20+i]=Z1[i];
		}
		// printf("###################################################################################\n\n");
		
		
		// printf("########################### ATTACK PROCEDURE: RECOVER KEY ########################\n");
		// printf("...\n\n");
		//Exhaustively search all the guessed key bits, and recover them
		double cor_max=0.0; int iK_guessed_max=-1;//denote no value of guessed key with non-zero correlation
		for(int iK_guessed=0;iK_guessed<(1<<numKeyBitsGuessed);iK_guessed++){
			/*Assign initial state:
				set the value of 8 guessed key bits and 
				fix the key bits in PNBs into zeros in X0 and X1.*/
			ECRYPT_ctx X0,X1;
			AssignInitS(&X0,subkey_known,iK_guessed,numKeyBitsGuessed);
			AssignInitS(&X1,subkey_known,iK_guessed,numKeyBitsGuessed);

			uint64_t ctr=0;
			for(uint64_t iIV=0;iIV<N_total;iIV++){
				//obtain IV
				uint32_t iv0[4],iv1[4];
				int i;
				for(i=0;i<4;i++) iv0[i]=dataIO[iIV][i];
				iv1[0]=iv0[0];
				iv1[2]=iv0[2];
				iv1[3]=iv0[3];
				iv1[1]=iv0[1]^((uint32_t)1<<ID_indexBit);//assert(ID_indexWord==1);
				ECRYPT_ivsetup32(&X0,iv0);
				ECRYPT_ivsetup32(&X1,iv1);

				//backward compuation
				uint32_t X0_end[16],X0_mid[16];
				uint32_t X1_end[16],X1_mid[16];
				for(i=0;i<16;i++){
					X0_end[i]=dataIO[iIV][4+i]-X0.input[i];
					X1_end[i]=dataIO[iIV][20+i]-X1.input[i];
				}
				chacha_invRounds_reduced_half(X0_mid,X0_end,numCipher,numDiff);
				chacha_invRounds_reduced_half(X1_mid,X1_end,numCipher,numDiff);
				if(GET_BIT(X0_mid[OD_indexWord],OD_indexBit)==GET_BIT(X1_mid[OD_indexWord],OD_indexBit)) ctr++;
			}
			double cor_tmp=CorrelationFormula(ctr,N_total);
			
			// if(flagDebug==1) printf("when iK_guessed = %d, correlation is %.4f\n", iK_guessed,cor_tmp);

			if(fabs(cor_tmp)>cor_max){
				cor_max=fabs(cor_tmp);
				iK_guessed_max=iK_guessed;
			}
		}
		// printf("################################################################################\n\n");

		for(i_data=0;i_data<N_total;i_data++) delete[] dataIO[i_data];
		delete[] dataIO;

		int valueKey=0;
		valueKey+=GET_BIT(key[0],6);
		valueKey+=GET_BIT(key[0],9) << 1;
		valueKey+=GET_BIT(key[0],10) << 2;
		valueKey+=GET_BIT(key[0],11) << 3;
		valueKey+=GET_BIT(key[0],12) << 4;
		valueKey+=GET_BIT(key[0],13) << 5;
		valueKey+=GET_BIT(key[0],18) << 6;
		valueKey+=GET_BIT(key[1],6) << 7;
		if(flagDebug==1) printf("True value of 8 guessed key bits is %d.\n",valueKey);
		if(flagDebug==1) printf("Guessed value with maximum correlation is %d.\n", iK_guessed_max);
		if(iK_guessed_max==valueKey) {
			if(flagDebug==1) printf("Successfully recover 8 guessed key bits!\n\n");
			ctrSucc+=1;
		}
		else if(flagDebug==1) printf("Failed to recover the key bits!\n\n");
	}
	
	printf("There are %d out of %d random keys are successfully recovered 8 guessed key bits.\n",ctrSucc,numK);
	printf("###################################### END #######################################\n\n");
}




int main(){
	time_t t;
	struct tm* lt;
	time(&t);
	lt=localtime(&t);
	printf("######## %d-%d-%d %d:%d:%d ########\n\n\n", lt->tm_year+1900, lt->tm_mon+1, lt->tm_mday, lt->tm_hour, lt->tm_min, lt->tm_sec);
	
	double total_t;//total used time
	struct timeval start_t,end_t;
	gettimeofday(&start_t,NULL);
		
	PraticalAttack_ChaCha5_withSyncopation();
	

	// PraticalAttack_ChaCha5_withoutSyncopation();
		
	gettimeofday(&end_t,NULL);
	total_t=(end_t.tv_sec-start_t.tv_sec) + (double)(end_t.tv_usec-start_t.tv_usec)/1000000.0;
	
	printf("Totally used time: %lf seconds.\n\n\n", total_t);

	return 0;
}