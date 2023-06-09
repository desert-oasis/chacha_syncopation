#include <stdint.h>


/*REFERENCE: https://en.wikipedia.org/wiki/Salsa20*/
#define ROTL(a,b) (((a) << (b)) | ((a) >> (32 - (b))))
#define QR(a, b, c, d) (					\
	a += b,  d ^= a,  d = ROTL(d,16),	\
	c += d,  b ^= c,  b = ROTL(b,12),	\
	a += b,  d ^= a,  d = ROTL(d, 8),	\
	c += d,  b ^= c,  b = ROTL(b, 7))
#define INV_QR(a, b, c, d) (		  		\
	b = ROTL(b,25),  b ^= c,  c -= d,	\
	d = ROTL(d,24),  d ^= a,  a -= b, 	\
	b = ROTL(b,20),  b ^= c,  c -= d, 	\
	d = ROTL(d,16),  d ^= a,  a -= b)
#define HALF_INV_QR(a,b,c,d) (	\
	b = ROTL(b,25),  b ^= c,  c -= d,	\
	d = ROTL(d,24),  d ^= a,  a -= b)
#define ROUNDS 20

void chacha_block(uint32_t out[16], uint32_t const in[16]){
	int i;
	uint32_t x[16];

	for (i = 0; i < 16; ++i)	
		x[i] = in[i];
	// 10 loops × 2 rounds/loop = 20 rounds
	for (i = 0; i < ROUNDS; i += 2) {
		// Odd round
		QR(x[0], x[4], x[ 8], x[12]); // column 0
		QR(x[1], x[5], x[ 9], x[13]); // column 1
		QR(x[2], x[6], x[10], x[14]); // column 2
		QR(x[3], x[7], x[11], x[15]); // column 3
		// Even round
		QR(x[0], x[5], x[10], x[15]); // diagonal 1 (main diagonal)
		QR(x[1], x[6], x[11], x[12]); // diagonal 2
		QR(x[2], x[7], x[ 8], x[13]); // diagonal 3
		QR(x[3], x[4], x[ 9], x[14]); // diagonal 4
	}
	for (i = 0; i < 16; ++i)
		out[i] = x[i] + in[i];
}

void chacha_block_reduced(uint32_t out[16], uint32_t const in[16], const int num_round){
	int i;
	uint32_t x[16];

	for (i = 0; i < 16; ++i) x[i] = in[i];
	// (num_round / 2) loops × 2 rounds/loop = num_round or num_round-1 rounds
	for (i = 0; i <= num_round-2; i += 2){
		// Odd round
		QR(x[0], x[4], x[ 8], x[12]); // column 0
		QR(x[1], x[5], x[ 9], x[13]); // column 1
		QR(x[2], x[6], x[10], x[14]); // column 2
		QR(x[3], x[7], x[11], x[15]); // column 3
		// Even round
		QR(x[0], x[5], x[10], x[15]); // diagonal 1 (main diagonal)
		QR(x[1], x[6], x[11], x[12]); // diagonal 2
		QR(x[2], x[7], x[ 8], x[13]); // diagonal 3
		QR(x[3], x[4], x[ 9], x[14]); // diagonal 4
	}
	if((num_round%2)==1){
		QR(x[0], x[4], x[ 8], x[12]); // column 0
		QR(x[1], x[5], x[ 9], x[13]); // column 1
		QR(x[2], x[6], x[10], x[14]); // column 2
		QR(x[3], x[7], x[11], x[15]); // column 3
	}

	for (i = 0; i < 16; ++i) out[i] = x[i] + in[i];
}

void chacha_invRounds_reduced_half(uint32_t out[16],uint32_t const in[16],const int numTarget,const int numDL){
	int i;
	uint32_t x[16];

	for (i = 0; i < 16; ++i) x[i] = in[i];
	// ((numTarget-numDL) / 2) loops × 2 rounds/loop = numTarget-numDL or (numTarget-numDL)-1 rounds
	if((numTarget%2)==1){
		for (i = 0; i <= (numTarget-numDL-2); i += 2){
			// Odd round
			INV_QR(x[0], x[4], x[ 8], x[12]); // column 0
			INV_QR(x[1], x[5], x[ 9], x[13]); // column 1
			INV_QR(x[2], x[6], x[10], x[14]); // column 2
			INV_QR(x[3], x[7], x[11], x[15]); // column 3
			// Even round
			INV_QR(x[0], x[5], x[10], x[15]); // diagonal 1 (main diagonal)
			INV_QR(x[1], x[6], x[11], x[12]); // diagonal 2
			INV_QR(x[2], x[7], x[ 8], x[13]); // diagonal 3
			INV_QR(x[3], x[4], x[ 9], x[14]); // diagonal 4
		}
	}
	else{
		for(i=0;i<=(numTarget-numDL-2);i+=2){
			// Even round
			INV_QR(x[0], x[5], x[10], x[15]); // diagonal 1 (main diagonal)
			INV_QR(x[1], x[6], x[11], x[12]); // diagonal 2
			INV_QR(x[2], x[7], x[ 8], x[13]); // diagonal 3
			INV_QR(x[3], x[4], x[ 9], x[14]); // diagonal 4
			// Odd round
			INV_QR(x[0], x[4], x[ 8], x[12]); // column 0
			INV_QR(x[1], x[5], x[ 9], x[13]); // column 1
			INV_QR(x[2], x[6], x[10], x[14]); // column 2
			INV_QR(x[3], x[7], x[11], x[15]); // column 3
		}
	}
	
	if(((numTarget-numDL)%2)==1){
		if(((numDL+1)%2)==1){
			// Odd round
			INV_QR(x[0], x[4], x[ 8], x[12]); // column 0
			INV_QR(x[1], x[5], x[ 9], x[13]); // column 1
			INV_QR(x[2], x[6], x[10], x[14]); // column 2
			INV_QR(x[3], x[7], x[11], x[15]); // column 3
		}
		else{
			// Even round
			INV_QR(x[0], x[5], x[10], x[15]); // diagonal 1 (main diagonal)
			INV_QR(x[1], x[6], x[11], x[12]); // diagonal 2
			INV_QR(x[2], x[7], x[ 8], x[13]); // diagonal 3
			INV_QR(x[3], x[4], x[ 9], x[14]); // diagonal 4
		}
	}
	
	if((numDL+1)%2==1){
		//Even half round
		HALF_INV_QR(x[0], x[5], x[10], x[15]); // diagonal 1 (main diagonal)
		HALF_INV_QR(x[1], x[6], x[11], x[12]); // diagonal 2
		HALF_INV_QR(x[2], x[7], x[ 8], x[13]); // diagonal 3
		HALF_INV_QR(x[3], x[4], x[ 9], x[14]); // diagonal 4
	}
	else{
		//Odd half round
		HALF_INV_QR(x[0], x[4], x[ 8], x[12]); // column 0
		HALF_INV_QR(x[1], x[5], x[ 9], x[13]); // column 1
		HALF_INV_QR(x[2], x[6], x[10], x[14]); // column 2
		HALF_INV_QR(x[3], x[7], x[11], x[15]); // column 3
	}

	for (i = 0; i < 16; ++i) out[i] = x[i];
}


/*REFERENCE: https://cr.yp.to/chacha.html*/
typedef struct{
	uint32_t input[16];
} ECRYPT_ctx;
void ECRYPT_keysetup32(ECRYPT_ctx *x,const uint32_t *k){
	x->input[0] = 0x61707865;
	x->input[1] = 0x3320646e;
	x->input[2] = 0x79622d32;
	x->input[3] = 0x6b206574;
	
	for(int i=0;i<8;i++) x->input[4+i]=k[i];
}
void ECRYPT_ivsetup32(ECRYPT_ctx *x,const uint32_t *iv){
	for(int i=0;i<4;i++) x->input[12+i]=iv[i];
}