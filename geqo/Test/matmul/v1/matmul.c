/**
 * Matrix multiplication (CUDA Kernel) on the device: C = A * B
 * wA is A's width and wB is B's width
 */

#define BLOCK_SIZE 32

// (0,0) <= (tx,ty) <= (BLOCK_SIZE,BLOCK_SIZE/2)

void matrixMulCUDA(int *C, int *A, int *B, int wA, int wB,
    int bx, int by, // Block index
    int tx, int ty // Thread index
    ) 
{
	// Index of the first sub-matrix of A processed by the block
	int aBegin = wA * BLOCK_SIZE * by;

	// Index of the last sub-matrix of A processed by the block
	int aEnd   = aBegin + wA - 1;

	// Step size used to iterate through the sub-matrices of A
	int aStep  = BLOCK_SIZE;

	// Index of the first sub-matrix of B processed by the block
	int bBegin = BLOCK_SIZE * bx;

	// Step size used to iterate through the sub-matrices of B
	int bStep  = BLOCK_SIZE * wB;

	// Csub is used to store the element of the block sub-matrix
	// that is computed by the thread 
	int Csub = 0, Csub2 = 0;

    // Loop over all the sub-matrices of A and B
    // required to compute the block sub-matrix
    for (int a = aBegin, b = bBegin;
         a <= aEnd;
         a += aStep, b += bStep)
    {
        // Declaration of the shared memory array As used to
        // store the sub-matrix of A
        int As[BLOCK_SIZE][BLOCK_SIZE];

        // Declaration of the shared memory array Bs used to
        // store the sub-matrix of B
        int Bs[BLOCK_SIZE][BLOCK_SIZE];

    	// Load the matrices from device memory
        // to shared memory; each thread loads
        // one element of each matrix
        As[ty][tx] = A[a + wA * ty + tx];
        Bs[ty][tx] = B[b + wB * ty + tx];
        As[ty+16][tx] = A[a + wA * (ty+16) + tx];
        Bs[ty+16][tx] = B[b + wB * (ty+16) + tx];        

        // Multiply the two matrices together;
        // each thread computes one element
        // of the block sub-matrix

        for (int k = 0; k < BLOCK_SIZE; ++k)
        {
            Csub += As[ty][k] * Bs[k][tx];
            Csub2 += As[ty+16][k] * Bs[k][tx];
        }

        // Synchronize to make sure that the preceding
        // computation is done before loading two new
        // sub-matrices of A and B in the next iteration
        //__syncthreads();

	}
	int c = wB * BLOCK_SIZE * by + BLOCK_SIZE * bx;
	C[c + wB * ty + tx] = Csub;
	C[c + wB * (ty+16) + tx] = Csub2;
}

