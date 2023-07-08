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
//PARAMETERS
#define SIZE_STATE 512
#define SIZE_KEY 256
#define SIZE_WORD 32
#define SIZE_BYTE 8

//FUNCTIONS
#define GET_BIT(a,p) (((a)>>(p))&0x1)


/*Random number generator*/
mt19937 gen((unsigned int) time(NULL)); //seed random generator every time


/*parameter used in the sampling experiment for estimate the correlation (not bias) of 
	backwards PNB-based approximation.*/
uint64_t NIV;
/*the number of random keys*/
uint64_t NK;


int wt_cut=13;
int flag74or89=1;//0 for 74 CPNBs; 1 for 89 CPNBs
/*The following order of conditions is to traverse first the conditions with type 0, then the conditions with type 1 and 2.*/
int i_cut_74[SIZE_KEY]={8,11,15,16,17,18,19,20,22,23,24,25,26,SIZE_KEY};  // 74 PNBs
int i_cut_89[SIZE_KEY]={14,17,24,25,26,28,29,31,32,35,36,38,39,SIZE_KEY};  // 89 PNBs
int pos_Max=0, pos_gap=7;

int cut_condition(int j, int n){   // n: numSyncopatedSegments
	assert((flag74or89==0) | (flag74or89==1));
	for(int i=0;i<min(wt_cut+1,n);i++){
		if(flag74or89==0){
			if (j==i_cut_74[i]) return 1;
		}
		else{
			if (j==i_cut_89[i]) return 1;
		}
	}
	return 0;
}

/*MISCS*/
void GetRandomUint32(uint32_t *r,int lenWords){
	for(int i=0;i<lenWords;i++) r[i]=gen();
}

void PrintState(uint32_t s[16]){
	for(int i=0;i<16;i++){
		// std::cout<<std::hex<<std::setfill('0')<<std::setw(8)<<int(s[i])<<" ";
		// if((i+1)%4==0) std::cout<<std::endl;
		printf("%08x ", s[i]);
		if((i+1)%4==0) printf("\n");
	}
	// std::cout<<std::endl;
	printf("\n");
}

double CorrelationFormula(uint64_t occurrence,uint64_t NS){
	return 2.0*((double)occurrence/(double)NS)-1.0;
}
/*descending sort*/
void BubbleSortABS(double *arr,int len){
	double temp;
	int numSorted,indexToBubble;

	for(numSorted=0;numSorted<len-1;numSorted++)
		for(indexToBubble=0;indexToBubble<len-numSorted-1;indexToBubble++)
			if(fabs(arr[indexToBubble])<fabs(arr[indexToBubble+1])){
				temp=arr[indexToBubble];
				arr[indexToBubble]=arr[indexToBubble+1];
				arr[indexToBubble+1]=temp;
			}
}
double GetMedianABS(double *array,uint64_t NS){
	BubbleSortABS(array,NS);
	if(NS%2==1) return array[NS/2];
	else return (0.5*(fabs(array[NS/2])+fabs(array[NS/2-1])));
}

int GetZeroRuns_InWord(int zeroRuns[SIZE_KEY][2],int signPNB[SIZE_KEY]){
	int flagDetails=0; 
	
	if(flagDetails==1){
		for(int i=0;i<SIZE_KEY;i++){
			printf("%d",signPNB[i]);
			if((i+1)%SIZE_WORD==0) printf("\n");
		}
	}

	int numZeorRuns=0;

	for(int i=0;i<8;i++){
		//first get the run length code in the current word
		int runLengthCode_word[SIZE_WORD][2];
		int numRuns_word=0;
		int runLength=0;
		int currentChar=signPNB[(i*SIZE_WORD)+0];
		for(int j=0;j<SIZE_WORD;j++){
			int indexKeyBit=i*SIZE_WORD+j;
			
			if(signPNB[indexKeyBit]==currentChar) runLength++;
			else{
				runLengthCode_word[numRuns_word][0]=currentChar;
				runLengthCode_word[numRuns_word][1]=runLength;
				numRuns_word++;
				
				currentChar=signPNB[indexKeyBit];
				runLength=1;
			}
		}
		runLengthCode_word[numRuns_word][0]=currentChar;
		runLengthCode_word[numRuns_word][1]=runLength;
		numRuns_word++;
		if(flagDetails==1) printf("numRuns_word is %d, run runLength code:\n",numRuns_word);

		//then get the zero-runs in the run length code of current word
		int index_word=0;
		for(int j=0;j<numRuns_word;j++){
			if(flagDetails==1) printf("(%d,%d) ",runLengthCode_word[j][0],runLengthCode_word[j][1]);
			if(runLengthCode_word[j][0]==0){
				zeroRuns[numZeorRuns][0]=i*SIZE_WORD+index_word;
				zeroRuns[numZeorRuns][1]=runLengthCode_word[j][1];

				numZeorRuns++;
			}
			
			index_word+=runLengthCode_word[j][1];
		}
		if(flagDetails==1) printf("\n");
		assert(index_word==SIZE_WORD);
	}

	return numZeorRuns;
}
void DetermineSyncopatedSegment(int signPNB[SIZE_KEY],int signPNB_syncopation[SIZE_KEY],int numSyncopatedSegments[2],int theta[2],int indexRestrictedSegments[SIZE_KEY][2],int syncopatedSegments[SIZE_KEY][2]){	
	/*In the following, the positions only work for ChaCha7, we identify it by "for ChaCha7".*/
	int flagDetails=0;
	// int flagDetails=1;

	for(int ik=0;ik<SIZE_KEY;ik++) signPNB_syncopation[ik]=signPNB[ik];
	
	//First, find all the possible zero run-lengths word by word
	int zeroRuns[SIZE_KEY][2];
	int numZeorRuns=GetZeroRuns_InWord(zeroRuns,signPNB);

	//Second, determine the syncopated segments and restricted segments (in the secret key) where we apply the syncopation technique
	if(flagDetails==1) printf("		-- the syncopated segments of secret key where the syncopation technique are applied: \n");
	numSyncopatedSegments[0]=0; //numSyncopatedSegments_secret_key
	numSyncopatedSegments[1]=0; //and numSyncopatedSegments_all
	theta[0]=0; // number of syncopated segments with two-bit restriction/condition
	theta[1]=0; // number of syncopated segments with one-bit restriction/condition
	for(int i=0;i<numZeorRuns;i++){
		//No need to apply the syncopation technique in the begining
		if(zeroRuns[i][0]%SIZE_WORD!=0){
			if(zeroRuns[i][1]>=2){
				if( ((zeroRuns[i][0]+2)-(zeroRuns[i][0]/SIZE_WORD)*SIZE_WORD) < SIZE_WORD ){ //exclue the case we obtain no grain by imposing two-bit restrictions/conditions
					/*Still impose one-bit restriction/condition in this case, 
						One more key bit is used to update the value instead of filtering the data.*/
					signPNB_syncopation[zeroRuns[i][0]]=2;
					//index for restricted segments of key bits in state
					indexRestrictedSegments[numSyncopatedSegments[0]][0]=1;
					indexRestrictedSegments[numSyncopatedSegments[0]][1]=128+zeroRuns[i][0];
	 				syncopatedSegments[numSyncopatedSegments[0]][0]=128+zeroRuns[i][0]+1;
	 				syncopatedSegments[numSyncopatedSegments[0]][1]=zeroRuns[i][1]-1;

	 				numSyncopatedSegments[0]++;
	 				//for ChaCha7
	 				if(zeroRuns[i][0]/SIZE_WORD<4){
	 					theta[1]++;
	 				}
	 				else {
	 					theta[1]+=3;
	 				}
					if(zeroRuns[i][0]/SIZE_WORD<4) numSyncopatedSegments[1]++;
					else numSyncopatedSegments[1]+=3;

					// signPNB_syncopation[zeroRuns[i][0]]=2;
					// signPNB_syncopation[zeroRuns[i][0]+1]=2;
					// //index for restricted segments of key bits in state
					// indexRestrictedSegments[numSyncopatedSegments[0]][0]=2;
					// indexRestrictedSegments[numSyncopatedSegments[0]][1]=128+zeroRuns[i][0];
	 			// 	syncopatedSegments[numSyncopatedSegments[0]][0]=128+zeroRuns[i][0]+2;
	 			// 	syncopatedSegments[numSyncopatedSegments[0]][1]=zeroRuns[i][1]-2;

					// numSyncopatedSegments[0]++;
					// //for ChaCha7
	 			// 	if(zeroRuns[i][0]/SIZE_WORD<4){
	 			// 		theta[0]++;
	 			// 	}
	 			// 	else {
	 			// 		theta[0]+=3;
	 			// 	}
					// if(zeroRuns[i][0]/SIZE_WORD<4) numSyncopatedSegments[1]++;
					// else numSyncopatedSegments[1]+=3;
				}
				else{ // impose one-bit restriction/condition in this case
					signPNB_syncopation[zeroRuns[i][0]]=2;
					//index for restricted segments of key bits in state
					indexRestrictedSegments[numSyncopatedSegments[0]][0]=1;
					indexRestrictedSegments[numSyncopatedSegments[0]][1]=128+zeroRuns[i][0];
 					syncopatedSegments[numSyncopatedSegments[0]][0]=128+zeroRuns[i][0]+1;
 					syncopatedSegments[numSyncopatedSegments[0]][1]=zeroRuns[i][1]-1;
					// printf("		-- '+2' is beyond the current word, and new segment is (%d,%d).\n",\
						// syncopatedSegments[numSyncopatedSegments[0]][0],\
						// syncopatedSegments[numSyncopatedSegments[0]][1]);

 					numSyncopatedSegments[0]++;
 					//for ChaCha7
	 				if(zeroRuns[i][0]/SIZE_WORD<4){
	 					theta[1]++;
	 				}
	 				else {
	 					theta[1]+=3;
	 				}
					if(zeroRuns[i][0]/SIZE_WORD<4) numSyncopatedSegments[1]++;
					else numSyncopatedSegments[1]+=3;
				}
			}
			else{ // zeroRuns[i][1]=1, and can only impose one-bit restriction/condition in this case
				if( ((zeroRuns[i][0]+1)-(zeroRuns[i][0]/SIZE_WORD)*SIZE_WORD) < SIZE_WORD ){ //exclue the case we obtain no grain by imposing one-bit restrictions/conditions
					signPNB_syncopation[zeroRuns[i][0]]=2;
					//index for restricted segments of key bits in state
					indexRestrictedSegments[numSyncopatedSegments[0]][0]=1;
					indexRestrictedSegments[numSyncopatedSegments[0]][1]=128+zeroRuns[i][0];
	 				syncopatedSegments[numSyncopatedSegments[0]][0]=128+zeroRuns[i][0]+1;
	 				syncopatedSegments[numSyncopatedSegments[0]][1]=zeroRuns[i][1]-1;

	 				numSyncopatedSegments[0]++;
	 				//for ChaCha7
	 				if(zeroRuns[i][0]/SIZE_WORD<4){
	 					theta[1]++;
	 				}
	 				else {
	 					theta[1]+=3;
	 				}
					if(zeroRuns[i][0]/SIZE_WORD<4) numSyncopatedSegments[1]++;
					else numSyncopatedSegments[1]+=3;
				}
				// else{
					// printf("		-- '+1' is beyond the current word.\n");
				// }
			}
			if(flagDetails==1) 
				if(numSyncopatedSegments[0]>0)
					printf("			--> %d-th restricted position of secret key (%d-bit restricted segment), at %d, and segment is (%d,%d)\n",\
						numSyncopatedSegments[0],indexRestrictedSegments[numSyncopatedSegments[0]-1][0],
						indexRestrictedSegments[numSyncopatedSegments[0]-1][1]-128,\
						syncopatedSegments[numSyncopatedSegments[0]-1][0]-128,\
						syncopatedSegments[numSyncopatedSegments[0]-1][1]);
		}
	}
	assert( (theta[0]+theta[1])==numSyncopatedSegments[1] );

	//for ChaCha7
	pos_Max=numSyncopatedSegments[1]; // +++++ for cutting Conditions +++++
	pos_gap=(pos_Max-numSyncopatedSegments[0])/2; // +++++ for cutting Conditions +++++

	if(flagDetails==1) printf("		-- total %d syncopation positions for all, and %d for secret key.\n\n",numSyncopatedSegments[1],numSyncopatedSegments[0]);
}

void FixPNBs(ECRYPT_ctx *pX,const uint32_t *k,const int arrayPNBs[SIZE_KEY],const int numPNBs){
	pX->input[0] = 0x61707865;
	pX->input[1] = 0x3320646e;
	pX->input[2] = 0x79622d32;
	pX->input[3] = 0x6b206574;

	for(int i=0;i<8;i++) pX->input[4+i]=k[i];
	
	/*fix the key bits of PNBs into zero*/
	for(int i=0;i<numPNBs;i++){
		int pWord=4+(arrayPNBs[i]/SIZE_WORD);
		uint32_t tmpV=((uint32_t)1)<<(arrayPNBs[i]%SIZE_WORD);
		pX->input[pWord]=(pX->input[pWord]) & (~tmpV);//set the fixed bit into zero
	}
}

void UpdateSyncopatedSegments(int labelType,uint32_t XX[16],uint32_t X[16],uint32_t initX[16],uint32_t ZZ[16],int numSyncopatedSegments,int syncopatedSegments[SIZE_KEY][2]){
	for(int i=0;i<numSyncopatedSegments;i++) {

		// ++++++++ cutting down the number of conditions   ++++++++
		if(cut_condition(i+pos_gap*labelType,pos_Max)==1){
			continue;
		}
		// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		int pWord=syncopatedSegments[i][0]/SIZE_WORD;
		int pBit=syncopatedSegments[i][0]%SIZE_WORD;
		
		assert((pWord>=4) & (pWord<12));
		if(labelType){
			if(pWord<8) continue;
		}

		uint32_t tmpW=0;
		for(int j=0;j<syncopatedSegments[i][1];j++){ 
			tmpW = tmpW | ((uint32_t)1<<(pBit+j));
		}		
		uint32_t tmpWV=X[pWord]&tmpW;
		XX[pWord]=( XX[pWord] & (~tmpW) ) ^ tmpWV; //set the value of syncopated segments into X due to Lemma 2

		//set the value of carry bit after the syncopated segments due to Lemma 2
		int tmpIndex=pBit+syncopatedSegments[i][1];
		if(tmpIndex<SIZE_WORD) {
			uint32_t tmpValueCarry=(uint32_t)1<<tmpIndex;
			uint32_t tmpMask=tmpValueCarry-1;
			int carryBit=((initX[pWord]&tmpMask)+(X[pWord]&tmpMask))/tmpValueCarry;
			int yBit=GET_BIT(ZZ[pWord],tmpIndex);
			int tmpV=carryBit^yBit;
			uint32_t tmpWV=((uint32_t)tmpV)<<tmpIndex;
			XX[pWord]=( XX[pWord] & (~tmpValueCarry) ) ^ tmpWV;
		}
	}
}
void InvertLastRound_theoretical(int flagSYNC,uint32_t X_internal[16],uint32_t XX_internal[16],uint32_t X_end[16],uint32_t XX_end[16],uint32_t initX[16],uint32_t Z[16],int numSyncopatedSegments,int syncopatedSegments[SIZE_KEY][2]){
	/*In the following, the positions only work for ChaCha7, we identify it by "for ChaCha7".*/
	uint32_t ZZ[16];
	int i;
	for(i=4;i<12;i++) ZZ[i]=Z[i];
	
	/*<0. update the values of syncopated segments according to the syncopation technique, for ChaCha7*/
	if(flagSYNC==1) UpdateSyncopatedSegments(0,XX_end,X_end,initX,ZZ,numSyncopatedSegments,syncopatedSegments);
	

	uint32_t X_tmp[16];
	uint32_t XX_tmp[16];
	for(i=0;i<16;i++){
		X_tmp[i]=X_end[i];
		XX_tmp[i]=XX_end[i];
	}

	//"inverse" half round at the last second branch, for ChaCha7
	for(i=8;i<12;i++) ZZ[i]=Z[i]-XX_end[i+4];
	//Odd half round, for ChaCha7
	HALF_INV_QR(X_tmp[0], X_tmp[4], X_tmp[ 8], X_tmp[12]); // column 0
	HALF_INV_QR(X_tmp[1], X_tmp[5], X_tmp[ 9], X_tmp[13]); // column 1
	HALF_INV_QR(X_tmp[2], X_tmp[6], X_tmp[10], X_tmp[14]); // column 2
	HALF_INV_QR(X_tmp[3], X_tmp[7], X_tmp[11], X_tmp[15]); // column 3
	HALF_INV_QR(XX_tmp[0], XX_tmp[4], XX_tmp[ 8], XX_tmp[12]); // column 0
	HALF_INV_QR(XX_tmp[1], XX_tmp[5], XX_tmp[ 9], XX_tmp[13]); // column 1
	HALF_INV_QR(XX_tmp[2], XX_tmp[6], XX_tmp[10], XX_tmp[14]); // column 2
	HALF_INV_QR(XX_tmp[3], XX_tmp[7], XX_tmp[11], XX_tmp[15]); // column 3

	/*<1. update the values of syncopated segments according to the syncopation technique, for ChaCha7*/
	if(flagSYNC==1) UpdateSyncopatedSegments(1,XX_tmp,X_tmp,initX,ZZ,numSyncopatedSegments,syncopatedSegments);


	//"inverse" one round at the last second branch, for ChaCha7
	for(i=8;i<12;i++) ZZ[i]=Z[i]-XX_end[i+4]-XX_tmp[i+4];
	//Odd half round, for ChaCha7
	HALF_INV_QR2(X_tmp[0], X_tmp[4], X_tmp[ 8], X_tmp[12]); // column 0
	HALF_INV_QR2(X_tmp[1], X_tmp[5], X_tmp[ 9], X_tmp[13]); // column 1
	HALF_INV_QR2(X_tmp[2], X_tmp[6], X_tmp[10], X_tmp[14]); // column 2
	HALF_INV_QR2(X_tmp[3], X_tmp[7], X_tmp[11], X_tmp[15]); // column 3
	for(i=0;i<16;i++) X_internal[i]=X_tmp[i];
	HALF_INV_QR2(XX_tmp[0], XX_tmp[4], XX_tmp[ 8], XX_tmp[12]); // column 0
	HALF_INV_QR2(XX_tmp[1], XX_tmp[5], XX_tmp[ 9], XX_tmp[13]); // column 1
	HALF_INV_QR2(XX_tmp[2], XX_tmp[6], XX_tmp[10], XX_tmp[14]); // column 2
	HALF_INV_QR2(XX_tmp[3], XX_tmp[7], XX_tmp[11], XX_tmp[15]); // column 3
	for(i=0;i<16;i++) XX_internal[i]=XX_tmp[i];
	
	/*<2. update the values of syncopated segments according to the syncopation technique, for ChaCha7*/
	if(flagSYNC==1) UpdateSyncopatedSegments(2,XX_internal,X_internal,initX,ZZ,numSyncopatedSegments,syncopatedSegments);
}
double EstimateApproxCPNBs_single_theoretical(double numIVsExp,double num_target,double num_diff,int indexOD, int arrayPNBs[SIZE_KEY],int numPNBs, int syncopatedSegments[SIZE_KEY][2], int numSyncopatedSegments){
	int detailedInfos=1;
	/*whether to use the syncopation technique or not.*/
	int flagSYNC=1;

	NK=((uint64_t)1<<10);
	if(detailedInfos==1) printf("	- number of keys: 2^{%.0f}\n",log(NK)/log(2));
	NIV=(uint64_t)pow(2,numIVsExp);
	if(detailedInfos==1) printf("	- number of IVs: 2^{%.1f}\n",log(NIV)/log(2));
	
	assert((num_target==7.0) & (num_diff==3.5));
	int numTarget=(int)num_target;//floor
	int numDL=ceil(num_diff);
	
	double res=0.0;
	double cor[NK]; //static array no greater than 64K = 2^16 bytes
	uint64_t ctr[NK]; //static array no greater than 64K = 2^16 bytes
	memset(ctr,0,NK*sizeof(uint64_t));

	for(uint64_t iKey=0;iKey<NK;iKey++){
		ECRYPT_ctx X;
		uint32_t key[8];
		GetRandomUint32(key,8);
		ECRYPT_keysetup32(&X,key);
		
		/*fix the key bits in PNBs into zero in X*/
		ECRYPT_ctx XX;
		FixPNBs(&XX,key,arrayPNBs,numPNBs);
		
		for(uint64_t iIV=0;iIV<NIV;iIV++){
			uint32_t iv[4];
			GetRandomUint32(iv,4);
			ECRYPT_ivsetup32(&X,iv);
			// PrintState(X.input);
			/*fix the key bits in PNBs into zero in X, and keep the the value of IV unchange.*/
			ECRYPT_ivsetup32(&XX,iv);
			// PrintState(XX.input);
			
			//compute Z
			uint32_t Z[16];
			chacha_block_reduced(Z,X.input,numTarget);
			
			uint32_t X_end[16],X_internal[16],X_mid[16];
			uint32_t XX_end[16],XX_internal[16],XX_mid[16];

			int i;
			
			for(i=0;i<16;i++){
				X_end[i]=Z[i]-X.input[i];
			}

			/*fix the key bits in PNBs into zero in X*/
			for(i=0;i<16;i++){
				XX_end[i]=Z[i]-XX.input[i];
			}
			

			/*Invert the state of last round on the premise that the values of syncopated segments are known with the syncopation technique*/
			assert(numTarget-1>=numDL);
			InvertLastRound_theoretical(flagSYNC,X_internal,XX_internal,X_end,XX_end,X.input,Z,numSyncopatedSegments,syncopatedSegments);


			// chacha_invRounds_reduced_half(X_mid,X_end,numTarget,numDL);
			chacha_invRounds_reduced_half(X_mid,X_internal,numTarget-1,numDL);
			//observe the value at the position of OD
			int tmpV0=GET_BIT(X_mid[indexOD/SIZE_WORD],indexOD%SIZE_WORD);

			// chacha_invRounds_reduced_half(XX_mid,XX_end,numTarget,numDL);
			chacha_invRounds_reduced_half(XX_mid,XX_internal,numTarget-1,numDL);
			//observe the value at the position of OD
			int tmpV1=GET_BIT(XX_mid[indexOD/SIZE_WORD],indexOD%SIZE_WORD);
			
			//XOR difference
			if(tmpV0==tmpV1) ctr[iKey]++;
		}
		
		cor[iKey]=CorrelationFormula(ctr[iKey],NIV);
		// if(detailedInfos==1) printf("correlation %lf (2^{%.4f}) for %ld-th key\n",cor[iKey],log(fabs(cor[iKey]))/log(2),iKey);
	}
	
	res=GetMedianABS(cor,NK);
	
	return res;
}

int CheckRestrictedConditions(uint32_t Z[16],uint32_t X[16],int numSyncopatedSegments,int indexRestrictedSegments[SIZE_KEY][2]){
	int res=1;

	/*In the following, the positions only work for ChaCha7, we identify it by "for ChaCha7".*/
	uint32_t X_end[16],X_internal[16];
	int w;
	for(w=0;w<4;w++) X_end[w]=Z[w]-X[w];
	for(w=12;w<16;w++) X_end[w]=Z[w]-X[w];
	//for ChaCha7, inverse half round at the last branch
	for(w=0;w<4;w++) X_internal[12+w] = ROTL(X_end[12+w],24) ^ X_end[w];

	for(int i=0;i<numSyncopatedSegments;i++){
		assert( (indexRestrictedSegments[i][1]>=128) & (indexRestrictedSegments[i][1]<384) );
		int pWord=indexRestrictedSegments[i][1]/SIZE_WORD;
		int pBit=indexRestrictedSegments[i][1]%SIZE_WORD;

		int valueX=0; //all values: 0,1,2,3
		int valueZ=0; //all values: 0,1,2,3
		int j;
		for(j=0;j<indexRestrictedSegments[i][0];j++){
			int bitX=GET_BIT(X[pWord],(pBit+j));
			int bitZ=GET_BIT(Z[pWord],(pBit+j));
			valueX=valueX^(bitX<<j);
			valueZ=valueZ^(bitZ<<j);
		}
		// ++++++++ cutting down the number of conditions   ++++++++
		if(valueX==valueZ && cut_condition(i,wt_cut)!=1){ //condition with type 0
			res=0;
			return res;
		}
		// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// if(valueX==valueZ){
		// 	res=0;
		// 	return res;
		// }

		if(pWord>=8){
			uint32_t ZZ;

			//ChaCha7, "inverse" half round at the last second branch
			ZZ=Z[pWord]-X_end[pWord+4];
			
			valueZ=0;
			for(j=0;j<indexRestrictedSegments[i][0];j++){
				int bitZ=GET_BIT(ZZ,(pBit+j));
				valueZ=valueZ^(bitZ<<j);
			}

			// ++++++++ cutting down the number of conditions   ++++++++
			if(valueX==valueZ && cut_condition(i+pos_gap,wt_cut)!=1){ //condition with type 1
				res=0;
				return res;
			}
			// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// if(valueX==valueZ){
			// 	res=0;
			// 	return res;
			// }

			//ChaCha7, "inverse" one round at the last second branch
			ZZ=Z[pWord]-X_end[pWord+4]-X_internal[pWord+4];

			valueZ=0;
			for(j=0;j<indexRestrictedSegments[i][0];j++){
				int bitZ=GET_BIT(ZZ,(pBit+j));
				valueZ=valueZ^(bitZ<<j);
			}
			// if(valueX==valueZ){
			// 	res=0;
			// 	return res;
			// }

			// ++++++++ cutting down the number of conditions   ++++++++
			if(valueX==valueZ && cut_condition(i+2*pos_gap,wt_cut)!=1){ //condition with type 2
				res=0;
				return res;
			}
			// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
		}
	}

	return res;
}
double EstimateApproxCPNBs_single(double numIVsExp,double num_target,double num_diff,int indexOD, int arrayPNBs[SIZE_KEY],int numPNBs, int numSyncopatedSegments, int theta[2],int indexRestrictedSegments[SIZE_KEY][2]){
	int detailedInfos=1;
	/*whether to use the syncopation technique or not.*/
	int flagSYNC=1;

	NK=((uint64_t)1<<6);
	if(detailedInfos==1) printf("	- number of keys: 2^{%.0f}\n",log(NK)/log(2));
	NIV=(uint64_t)pow(2,numIVsExp);
	if(detailedInfos==1) printf("	- number of IVs: 2^{%.1f}\n",log(NIV)/log(2));
	
	double ratioFiltered;
	if(flagSYNC==1) ratioFiltered=pow(0.5,theta[1]-wt_cut)*pow(0.75,theta[0]);
	else ratioFiltered=1.0;
	if(detailedInfos==1) printf("		-- ratio of filtering: 2^{-%.4lf}, ",-log(ratioFiltered)/log(2));
	double NUM_T_filtered_expected=(double)(NIV)*ratioFiltered;
	if(detailedInfos==1) printf("expected number of IVs: 2^{%.4lf}\n",log(NUM_T_filtered_expected)/log(2));

	assert((num_target==7.0) & (num_diff==3.5));
	int numTarget=(int)num_target;//floor
	int numDL=ceil(num_diff);
	
	double res=0.0;
	double cor[NK]; //static array no greater than 64K = 2^16 bytes
	uint64_t ctr[NK]; //static array no greater than 64K = 2^16 bytes
	memset(ctr,0,NK*sizeof(uint64_t));

	for(uint64_t iKey=0;iKey<NK;iKey++){
		ECRYPT_ctx X;
		uint32_t key[8];
		GetRandomUint32(key,8);
		ECRYPT_keysetup32(&X,key);
		
		/*fix the key bits in PNBs into zero in X*/
		ECRYPT_ctx XX;
		FixPNBs(&XX,key,arrayPNBs,numPNBs);
		
		int NUM_IV_filtered=0;
		for(uint64_t iIV=0;iIV<NIV;iIV++){
			uint32_t iv[4];
			GetRandomUint32(iv,4);
			ECRYPT_ivsetup32(&X,iv);
			// PrintState(X.input);
			/*fix the key bits in PNBs into zero in X, and keep the the value of IV unchange.*/
			ECRYPT_ivsetup32(&XX,iv);
			// PrintState(XX.input);
			
			//compute Z
			uint32_t Z[16];
			chacha_block_reduced(Z,X.input,numTarget);

			/*Check whether the restrictions/conditions on restricted segments hold.*/
			int flagRestrictedC;
			if(flagSYNC==1) flagRestrictedC=CheckRestrictedConditions(Z,X.input,numSyncopatedSegments,indexRestrictedSegments);
			else flagRestrictedC=1;


			if(flagRestrictedC==1){
				NUM_IV_filtered=NUM_IV_filtered+1;
				uint32_t X_end[16],X_mid[16];
				uint32_t XX_end[16],XX_mid[16];

				int i;
				
				for(i=0;i<16;i++){
					X_end[i]=Z[i]-X.input[i];
				}

				/*fix the key bits in PNBs into zero in X*/
				for(i=0;i<16;i++){
					XX_end[i]=Z[i]-XX.input[i];
				}
				
				/*With proposition 2, the values of syncopated segments are equal between g and f.*/
				
				chacha_invRounds_reduced_half(X_mid,X_end,numTarget,numDL);
				//observe the value at the position of OD
				int tmpV0=GET_BIT(X_mid[indexOD/SIZE_WORD],indexOD%SIZE_WORD);

				chacha_invRounds_reduced_half(XX_mid,XX_end,numTarget,numDL);
				//observe the value at the position of OD
				int tmpV1=GET_BIT(XX_mid[indexOD/SIZE_WORD],indexOD%SIZE_WORD);
				
				//XOR difference
				if(tmpV0==tmpV1) ctr[iKey]++;
			}
		}
		
		cor[iKey]=CorrelationFormula(ctr[iKey],NUM_IV_filtered);
		// if(detailedInfos==1) printf("	- correlation %lf (2^{%.4f}) for %ld-th key\n",cor[iKey],log(fabs(cor[iKey]))/log(2),iKey);
		// if(detailedInfos==1) printf("		-- NUM_IV_filtered is %d (2^{%.4lf})\n\n",NUM_IV_filtered,log(NUM_IV_filtered)/log(2));
	}
	
	res=GetMedianABS(cor,NK);
	
	return res;
}

void Verification_BackApprox(double rounds_target,double rounds_diff,int OD){
	int numCPNBs;
	double numIVsExp;

	assert((flag74or89==0) | (flag74or89==1));
	if(flag74or89==0){
		numCPNBs=74;
		numIVsExp=16.3;
	}
	else{
		numCPNBs=89;
		numIVsExp=20.3;
	}


	/*Read the CPNBs generated by Algorithm 2 from the file,*/
	int arrayCPNBs_file[numCPNBs];
	char filePath[1024];
	sprintf(filePath,"cpnbs_size%d_greedy.txt",numCPNBs);
	ifstream ifs(filePath,ios::binary|ios::in);
	if(ifs.is_open()){
		ifs.read((char *)arrayCPNBs_file,sizeof(int)*numCPNBs);
		ifs.close();
	}
	else{
		printf("\n\nFAILED TO OPEN FILE OF CPNBS!\n\n");
	}
	/*then reconstruct the CPNBs.*/
	int arrayCPNBs_final[SIZE_KEY];
	int numCPNBs_final=0;
	int signCPNB_final[SIZE_KEY];
	int i;
	for(i=0;i<numCPNBs;i++){
		arrayCPNBs_final[numCPNBs_final]=arrayCPNBs_file[i];
		numCPNBs_final++;
	}
	assert(numCPNBs_final==numCPNBs);
	for(i=0;i<SIZE_KEY;i++) signCPNB_final[i]=0;
	for(i=0;i<numCPNBs_final;i++) signCPNB_final[arrayCPNBs_final[i]]=1;

	/*Algorithm 1: determine syncopated segments and restricted segments.*/
	int numSyncopatedSegments[2];
	int indexRestrictedSegments[SIZE_KEY][2];
	int syncopatedSegments[SIZE_KEY][2];
	int signCPNB_syncopation[SIZE_KEY];
	int theta[2];
	DetermineSyncopatedSegment(signCPNB_final,signCPNB_syncopation,numSyncopatedSegments,theta,indexRestrictedSegments,syncopatedSegments);
	

	/*According to Lemmas 1 and 2, under the condition that equations are satisfied, the syncopated segments are independent with PNBs and known.
		Thus, theoretically estimate the backward correlation on the premise that the values of syncopated segments are known.*/
	double epsilon_a_abs_median_single=EstimateApproxCPNBs_single_theoretical(numIVsExp,rounds_target,rounds_diff,OD,arrayCPNBs_final,numCPNBs_final,syncopatedSegments,numSyncopatedSegments[0]);
	printf("	- |\\epsilon'_a|=%lf (2^{%.4f})\n\n\n",epsilon_a_abs_median_single,log(epsilon_a_abs_median_single)/log(2));
	if(flag74or89==0){
		printf("	############## Re-verification Experiment for Theoretical Calculation of Backward Correlation ##################### \n");
		numIVsExp=32.6;
		epsilon_a_abs_median_single=EstimateApproxCPNBs_single(numIVsExp,rounds_target,rounds_diff,OD,arrayCPNBs_final,numCPNBs_final,numSyncopatedSegments[0],theta,indexRestrictedSegments);
		printf("	- |\\epsilon'_a|=%lf (2^{%.4f})\n\n\n",epsilon_a_abs_median_single,log(epsilon_a_abs_median_single)/log(2));
	}
}

/*TWO ATTACK PARAMETERS WITH 74 CPNBS OR 89 CPNBS*/
void AttackOnChaCha7(){
	double rounds_target=7;
	double rounds_diff=3.5;
	printf("Attacking %.1f rounds reduced ChaCha with %.1f rounds truncated differential and %.1f rounds backwards approximation equipped with syncopation technique:\n\n", rounds_target,rounds_diff,rounds_target-rounds_diff);
	
	printf("\n ###########################  BEGIN  ################################# \n\n");
	/*STEP 1: truncated difference in forwards direction*/
	int ID=1*32+6; //i.e., from 0 to 127
	int OD=2*32+0; //i.e., from 0 to 511
	double epsilon_d_abs=0.00317;
	printf("Forward characteristic of 3.5 rounds:\n");
	printf("	Single-bit differential ID at %d-th bit, and OD at (%d,%d)-th bit, with correlation of 2^{%.4f}.\n\n\n"\
		,ID,OD/SIZE_WORD,OD%SIZE_WORD,log(epsilon_d_abs)/log(2));


	/*STEP2: approximation with syncopation technique in backward direction*/
	printf("Backward approximation with syncopation technique of 3.5 rounds:\n");
	assert((flag74or89==0) | (flag74or89==1));
	if(flag74or89==0) printf("	With 74 CPNBs,\n\n");
	else printf("	With 89 CPNBs,\n\n");
	Verification_BackApprox(rounds_target,rounds_diff,OD);

	printf("\n #############################  END  ############################### \n\n\n");
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
	
	/*For verification experiments of 74 CPNBs, please set flag74or89=0; 
 	  	  				  			  89 CPNBs, please set flag74or89=1*/
	AttackOnChaCha7();
	
	gettimeofday(&end_t,NULL);
	total_t=(end_t.tv_sec-start_t.tv_sec) + (double)(end_t.tv_usec-start_t.tv_usec)/1000000.0;
	

	printf("Totally used time: %lf seconds.\n\n\n", total_t);
}