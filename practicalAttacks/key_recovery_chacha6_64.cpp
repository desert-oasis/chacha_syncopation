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
#define SIZE_WORD 32

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
const int numCipher=(int)6.0;
const int numDiff=ceil(3.5);

//Forward distinguisher
int ID_indexWord=1;
int ID_indexBit=6;
int OD_indexWord=2;
int OD_indexBit=0;
//Backward computation
int numKeyBitsGuessed=8;
int numConds=4; //with syncopation
//Data complexity
uint64_t N_star=pow(2,23.1);
uint64_t N_prime=N_star*(1<<(2*numConds));
uint64_t M=N_star*(1<<numConds);

int flagDebug=0;


int GetValue_SR(const uint32_t Z[16]){
	int res=0;

	res+=GET_BIT(Z[4],6);
	res+=GET_BIT(Z[5],6) << 1;
	res+=GET_BIT(Z[5],9) << 2;
	res+=GET_BIT(Z[5],18) << 3;

	return res;
}
void GenerateDataIO_E0(const uint32_t key[8], uint32_t **dataIO, uint64_t *numData_filtered){
	//Fix 32-bit value of IV at ID-column during one iteration of attack procedure
	uint32_t iv_ID=gen();
	for(uint64_t i_data=0;i_data<N_prime;i_data++){
		ECRYPT_ctx X0,X1;
		ECRYPT_keysetup32(&X0,key);
		ECRYPT_keysetup32(&X1,key);
		uint32_t iv0[4];
		uint32_t iv1[4];
		uint32_t tmp_iv[3];
		GetRandomUint32(tmp_iv,3);
		iv0[1]=iv_ID;
		iv1[1]=iv_ID^((uint32_t)1<<ID_indexBit); //assert(ID_indexWord==1);
		iv0[0]=tmp_iv[0];
		iv1[0]=tmp_iv[0];
		iv0[2]=tmp_iv[1];
		iv1[2]=tmp_iv[1];
		iv0[3]=tmp_iv[2];
		iv1[3]=tmp_iv[2];
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

uint32_t FindRightPair(uint32_t k1, uint32_t k5){
	int res=-1;

	const uint32_t NIV=(uint32_t)1<<31;
	int ID_indexBit=6;
	const int offset=ID_indexBit+1;//Note: input difference with ID_indexWord=1; ID_indexBit=6;
	//output difference
	uint32_t deltaX[4];
	deltaX[0]=1<<((ID_indexBit+28)%SIZE_WORD);
	deltaX[1]=(1<<((ID_indexBit+3)%SIZE_WORD)) | (1<<((ID_indexBit+11)%SIZE_WORD)) | (1<<((ID_indexBit+23)%SIZE_WORD)) | (1<<((ID_indexBit+31)%SIZE_WORD));
	deltaX[2]=(1<<((ID_indexBit+4)%SIZE_WORD)) | (1<<((ID_indexBit+16)%SIZE_WORD)) | (1<<((ID_indexBit+24)%SIZE_WORD));
	deltaX[3]=(1<<((ID_indexBit+4)%SIZE_WORD)) | (1<<((ID_indexBit+24)%SIZE_WORD));
	for(uint32_t iIV=0;iIV<NIV;iIV++){
		uint32_t X0[4],X1[4];
		//the second column
		X0[0]=0x3320646e;//c1
		X1[0]=0x3320646e;//c1
		X0[1]=k1;
		X0[2]=k5;
		X1[1]=k1;
		X1[2]=k5;
		X0[3]=ROTL(iIV,offset);
		X1[3]=ROTL((iIV^NIV),offset);
		
		//the quarterround in first round
		QR(X0[0],X0[1],X0[2],X0[3]);
		QR(X1[0],X1[1],X1[2],X1[3]);
		
		//check whether satisfy the fixed output difference
		int i;
		uint32_t tmp;
		for(i=0;i<4;i++) { //chane order to 1,2,3,0
			tmp=X0[i]^X1[i]^deltaX[i];
			if(tmp!=0){
				break;
			}
		}
		if(i==4) {
			res=iIV;
			break;
		}
	}

	return res;
}
int GenerateDataIO_E1(const uint32_t key[8], uint32_t **dataIO, uint64_t *numData_filtered){
	//Fix 32-bit value of IV at ID-column during one iteration of attack procedure
	uint32_t iv_ID;
	int ans=FindRightPair(key[1],key[5]); //set the right pair for the weak keys
	if(ans>=0) iv_ID=ROTL((uint32_t)ans,ID_indexBit+1);
	else {
		// printf("This key i.e., (k1,k5) is a strong key!\n");
		// exit(0);
		return 0;
	}
	for(uint64_t i_data=0;i_data<N_prime;i_data++){
		ECRYPT_ctx X0,X1;
		ECRYPT_keysetup32(&X0,key);
		ECRYPT_keysetup32(&X1,key);
		uint32_t iv0[4];
		uint32_t iv1[4];
		uint32_t tmp_iv[3];
		GetRandomUint32(tmp_iv,3);
		iv0[1]=iv_ID;
		iv1[1]=iv_ID^((uint32_t)1<<ID_indexBit); //assert(ID_indexWord==1);
		iv0[0]=tmp_iv[0];
		iv1[0]=tmp_iv[0];
		iv0[2]=tmp_iv[1];
		iv1[2]=tmp_iv[1];
		iv0[3]=tmp_iv[2];
		iv1[3]=tmp_iv[2];
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

	return 1;
}

int GetValue_kR(const int valueKeyBits){
	int res=0;

	//8 restricted key bits: {6, 38, 41, 50}, from LSB to MSB
	res+=GET_BIT(valueKeyBits,0);
	res+=GET_BIT(valueKeyBits,1) << 1;
	res+=GET_BIT(valueKeyBits,2) << 2;
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
	//8 guessed key bits: {6, 38, 41, 42, 43, 44, 45, 50}, from LSB to MSB
	pX->input[4]^=GET_BIT(valueKeyBits,0) << 6;
	pX->input[5]^=GET_BIT(valueKeyBits,1) << 6;
	pX->input[5]^=GET_BIT(valueKeyBits,2) << 9;
	pX->input[5]^=GET_BIT(valueKeyBits,3) << 10;
	pX->input[5]^=GET_BIT(valueKeyBits,4) << 11;
	pX->input[5]^=GET_BIT(valueKeyBits,5) << 12;
	pX->input[5]^=GET_BIT(valueKeyBits,6) << 13;
	pX->input[5]^=GET_BIT(valueKeyBits,7) << 18;
}
void ProcedureKeyRecovery_ChaCha6(const uint32_t *subkey_known, uint32_t **dataIO, uint64_t *numData_filtered, double res[2]){
	//STEP2: Exhaustively search all the guessed key bits, and recover them
	double cor_max=0.0; int iK_guessed_max=-1;
	double cor[1<<numKeyBitsGuessed];
	for(int iK_guessed=0;iK_guessed<(1<<numKeyBitsGuessed);iK_guessed++){
		//first, according to k^R, choose subsets in which element's values of S^R satisfying conditions
		int value_kR;
		value_kR=GetValue_kR(iK_guessed);
		int value_SR_Z=value_kR^0xf;//numConds=4
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
			assert(ID_indexWord==1);
			iv1[1]=iv0[1]^((uint32_t)1<<ID_indexBit);
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

		// if(flagDebug==1) printf("when %d, correlation is %.4f\n", iK_guessed,cor[iK_guessed]);
	}
	// if(flagDebug==1) printf("maximum of correlation is %.4f, when %d\n", cor_max,iK_guessed_max);
	res[0]=iK_guessed_max;
	res[1]=cor_max;
}

void PraticalAttack_ChaCha6_withSyncopation_E1(){
	int numK=32;
	int ctrWeak=0;
	int ctrSucc=0;

	printf("###################################### BEGIN #######################################\n\n");
	for(int iK=0;iK<numK;iK++){
	
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
	int flagAns=GenerateDataIO_E1(key,dataIO,numData_filtered);
	// printf("###################################################################################\n\n");
	
	
	if(flagAns==1){
	ctrWeak+=1;
	// printf("########################### ATTACK PROCEDURE: RECOVER KEY ########################\n");
	// printf("...\n\n");
	double ans[2];//value of 8 guessed key bits and corresponding correlation
	ProcedureKeyRecovery_ChaCha6(subkey_known,dataIO,numData_filtered,ans);
	// printf("################################################################################\n\n");


	int valueKey=0;
	valueKey+=GET_BIT(key[0],6);
	valueKey+=GET_BIT(key[1],6) << 1;
	valueKey+=GET_BIT(key[1],9) << 2;
	valueKey+=GET_BIT(key[1],10) << 3;
	valueKey+=GET_BIT(key[1],11) << 4;
	valueKey+=GET_BIT(key[1],12) << 5;
	valueKey+=GET_BIT(key[1],13) << 6;
	valueKey+=GET_BIT(key[1],18) << 7;
	if(flagDebug==1) printf("True value of 8 guessed key bits is %d.\n\n",valueKey);
	if((int)ans[0]==valueKey) {
		printf("Successfully recover 8 guessed key bits!\n\n");
		ctrSucc+=1;
	}
	
	}

	for(uint64_t i_data=0;i_data<M;i_data++) delete[] dataIO[i_data];
	delete[] dataIO;
	
	}

	printf("There are %d out of %d weak keys are successfully recovered 8 guessed key bits, total %d random keys.\n",ctrSucc,ctrWeak,numK);
	printf("###################################### END #######################################\n\n");
}

void PraticalAttack_ChaCha6_withSyncopation_E0(){
	int numK=16;
	int ctrSucc=0;

	printf("###################################### BEGIN #######################################\n\n");
	int iK;
	for(iK=0;iK<numK;iK++){

	//Secret key
	uint32_t key[8];
	GetRandomUint32(key,8);
	uint32_t subkey_known[6];
	for(int i=0;i<6;i++) subkey_known[i]=key[2+i];


	int numIterations=32;
	int valueK_max=-1; double cor_max=0.0;
	for(int iRepeat=0;iRepeat<numIterations;iRepeat++){
		// printf("############################# GENERATING DATA ######################################\n");
		// printf("...\n\n");
		//Array for storing data of input and output.
		uint32_t **dataIO=new uint32_t *[M];
		for(uint64_t i_data=0;i_data<M;i_data++) dataIO[i_data]=new uint32_t[4+2*16]; //(IV,Z0,Z1)
		uint64_t numData_filtered[1<<numConds];
		for(int i=0;i<(1<<numConds);i++) numData_filtered[i]=0;
		GenerateDataIO_E0(key,dataIO,numData_filtered);
		// printf("###################################################################################\n\n");
		
		
		// printf("########################### ATTACK PROCEDURE: RECOVER KEY ########################\n");
		// printf("...\n\n");
		double ans[2];//value of 8 guessed key bits and corresponding correlation
		ProcedureKeyRecovery_ChaCha6(subkey_known,dataIO,numData_filtered,ans);
		// printf("################################################################################\n\n");
		
		if(fabs(ans[1])>cor_max){
			cor_max=fabs(ans[1]);
			valueK_max=(int)ans[0];
		}

		for(uint64_t i_data=0;i_data<M;i_data++) delete[] dataIO[i_data];
		delete[] dataIO;
	}


	int valueKey=0;
	valueKey+=GET_BIT(key[0],6);
	valueKey+=GET_BIT(key[1],6) << 1;
	valueKey+=GET_BIT(key[1],9) << 2;
	valueKey+=GET_BIT(key[1],10) << 3;
	valueKey+=GET_BIT(key[1],11) << 4;
	valueKey+=GET_BIT(key[1],12) << 5;
	valueKey+=GET_BIT(key[1],13) << 6;
	valueKey+=GET_BIT(key[1],18) << 7;
	if(flagDebug==1) printf("True value of 8 guessed key bits is %d.\n\n",valueKey);
	if(flagDebug==1) printf("Maximum of correlation is %.4f for value %d\n", cor_max,valueK_max);
	if(valueK_max==valueKey) {
		printf("Successfully recover 8 guessed key bits!\n\n");
		ctrSucc+=1;
	}
	
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
	
	//Another experiment, first find right pair for weak keys, then recovery 8 guessed key bits	
	PraticalAttack_ChaCha6_withSyncopation_E1();
	

	// PraticalAttack_ChaCha6_withSyncopation_E0();

	gettimeofday(&end_t,NULL);
	total_t=(end_t.tv_sec-start_t.tv_sec) + (double)(end_t.tv_usec-start_t.tv_usec)/1000000.0;
	
	printf("Totally used time: %lf seconds.\n\n\n", total_t);

	return 0;
}