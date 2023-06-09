#include <stdio.h>
#include <iostream>
#include <time.h>
#include <string.h>
#include <math.h>
#include <random>
#include <cassert>
#include <fstream>
#include <bitset>
#include <sys/time.h>


using namespace std;


//ChaCha
#define ROTL(a,b) (((a) << (b)) | ((a) >> (32 - (b))))
#define QR(a, b, c, d) (					\
	a += b,  d ^= a,  d = ROTL(d,16),	\
	c += d,  b ^= c,  b = ROTL(b,12),	\
	a += b,  d ^= a,  d = ROTL(d, 8),	\
	c += d,  b ^= c,  b = ROTL(b, 7))


//PARAMETERS
#define SIZE_WORD 32

//FUNCTIONS
#define GET_BIT(a,p) (((a)>>(p))&0x1)


const uint32_t c0=0x61707865;
const uint32_t c1=0x3320646e;
const uint32_t c2=0x79622d32;
const uint32_t c3=0x6b206574;


/*Random number generator*/
mt19937 gen((unsigned int) time(NULL)); //seed random generator every time

/*MISCS*/
void GetRandomUint32(uint32_t *r,int lenWords){
	for(int i=0;i<lenWords;i++) r[i]=gen();
}


void PrintColumn(uint32_t x[4]){
	for(int i=0;i<4;i++) printf("%08x\n",x[i]);
	printf("\n\n");
}

int CheckRightPair(uint32_t inDiff,uint32_t outDiff[4],uint32_t key[2],uint32_t IV){
	uint32_t X0[4],X1[4];
	// //the first column
	// X0[0]=c0; 
	// X1[0]=c0;
	//the second column, which is used in CRYPTO20 and EC22
	X0[0]=c1;
	X1[0]=c1;
	
	X0[1]=key[0];
	X0[2]=key[1];
	X1[1]=X0[1];
	X1[2]=X0[2];
	// PrintColumn(X0);
	// PrintColumn(X1);

	//fixed input difference at 6-th bit
	X0[3]=IV;
	X1[3]=IV^inDiff;
	
	//the quarterround in first round
	QR(X0[0],X0[1],X0[2],X0[3]);
	QR(X1[0],X1[1],X1[2],X1[3]);

	//check whether satisfy the fixed output difference
	uint32_t tmp;
	int i;
	for(i=0;i<4;i++) { //chane order to 1,2,3,0
		tmp=X0[i]^X1[i]^outDiff[i];
		if(tmp!=0){
			break;
		}
	}
	
	if(i==4) return 1;
	else return 0;
}

uint32_t IndexMap_iIV(int iIV,uint32_t Vnonfree[SIZE_WORD],uint32_t dimVVnonfree){ //s1
	uint32_t IV=0;
	for(int i=0;i<dimVVnonfree-1;i++) IV|=(uint32_t)(GET_BIT(iIV,i))<<Vnonfree[i];
	// IV|=(uint32_t)(GET_BIT(iIV,dimVVnonfree-1))<<Vnonfree[dimVVnonfree-1];
	return IV;
}

void Verification(){
	/*the number of random keys*/
	const uint64_t NK=(uint64_t)1<<27;
	
	//index of input difference
	int indexID=6;
	const uint32_t inDiff=(uint32_t)1<<indexID;
	//output difference
	uint32_t outDiff[4];
	outDiff[0]=(uint32_t)1<<((indexID+28)%SIZE_WORD);
	outDiff[1]=((uint32_t)1<<((indexID+3)%SIZE_WORD)) | ((uint32_t)1<<((indexID+11)%SIZE_WORD)) | ((uint32_t)1<<((indexID+23)%SIZE_WORD)) | ((uint32_t)1<<((indexID+31)%SIZE_WORD));
	outDiff[2]=((uint32_t)1<<((indexID+4)%SIZE_WORD)) | ((uint32_t)1<<((indexID+16)%SIZE_WORD)) | ((uint32_t)1<<((indexID+24)%SIZE_WORD));
	outDiff[3]=((uint32_t)1<<((indexID+4)%SIZE_WORD)) | ((uint32_t)1<<((indexID+24)%SIZE_WORD));
	// for(int i=0;i<4;i++)printf("%08x\n",outDiff[i]);

	printf("########## Estimate the probability of weak keys which at least one IV is found in VV_{non-free} with V_{non-free}={0:5,14,26,30} #########\n\n");
	int Vnonfree_theoretical[10]={0,1,2,3,4,5,14,26,30,6};
	uint32_t dimVVnonfree_temp=10;
	uint32_t Vnonfree_temp[SIZE_WORD];
	for(int i=0;i<dimVVnonfree_temp-1;i++) Vnonfree_temp[i]=Vnonfree_theoretical[i];
	Vnonfree_temp[dimVVnonfree_temp-1]=indexID;
	uint32_t NIV=(uint32_t)1<<(dimVVnonfree_temp-1); //indexID is at the HSB
	printf("	dimVVnon-free=%d,\n",dimVVnonfree_temp-1);

	/*In VV_{non-free}, find an IV satisfy the right pair.*/
	int *favorableIV_temp=new int[NK];
	uint32_t **allKeys_temp=new uint32_t*[NK];
	for(uint64_t iKey=0;iKey<NK;iKey++) allKeys_temp[iKey]=new uint32_t[2];
	for (uint64_t iKey=0;iKey<NK;iKey++){
		favorableIV_temp[iKey]=-1;//denote no pairs of IV in VV_{non-free} satisfy the given difference.

		uint32_t key[2];
		GetRandomUint32(key,2);
		allKeys_temp[iKey][0]=key[0];
		allKeys_temp[iKey][1]=key[1];
		for(uint32_t iIV=0;iIV<NIV;iIV++){
			uint32_t tmp_X0_3=IndexMap_iIV(iIV,Vnonfree_temp,dimVVnonfree_temp);

			int flagFavorable=CheckRightPair(inDiff,outDiff,key,tmp_X0_3);
			if(flagFavorable==1){
				favorableIV_temp[iKey]=iIV;
				break;
			}
		}
	}

	uint64_t ctrWeakKeys_temp=0;
	for(uint64_t iKey=0;iKey<NK;iKey++){
		if(favorableIV_temp[iKey]>0){
			ctrWeakKeys_temp++;

			// /*retrieve the favorable IV*/
			// uint32_t v=(uint32_t)favorableIV_temp[iKey];
			// v=IndexMap_iIV(v,Vnonfree_temp,dimVVnonfree_temp);
			
			// printf("%ld-th weak key: ",ctrWeakKeys_temp);
			// printf("(%08x,%08x), and its one favorable IV: %08x\n",allKeys_temp[iKey][0],allKeys_temp[iKey][1],v);
		}
	}
	double p_exp_temp=(double)ctrWeakKeys_temp/(double)NK;
	printf("		- there are %ld weak keys out",ctrWeakKeys_temp);
	printf(" of %ld random uniformly keys,",NK); 
	printf(" the probability of weak keys is about %lf.\n\n",p_exp_temp);
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
	
	Verification();
	
	gettimeofday(&end_t,NULL);
	total_t=(end_t.tv_sec-start_t.tv_sec) + (double)(end_t.tv_usec-start_t.tv_usec)/1000000.0;
	
	printf("Totally used time: %lf seconds.\n\n\n", total_t);
}