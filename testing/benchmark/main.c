#include <stdio.h>


#if defined ( BASIC )
	#define ARG set
	#include "basic.h"
#elif defined ( RANK )
	#define ARG set
	#include "rank.h"
#elif defined ( SIZE )
	#define ARG set
	#include "size.h"
#elif defined ( COMPRESSION )
	#define ARG &set
	#include "compression.h"
#elif defined ( HALVING )
	#define ARG &set
	#include "halving.h"
#elif defined ( SPLITTING )
	#define ARG &set
	#include "splitting.h"
#else
	#define INVALID
#endif


#ifndef INVALID
void testValid ( void ) {
	DisjointSet * set = NULL;

	for ( int i = 1; i <= 10; i ++ ) {
    	makeSet ( i, & set );
	}

	int setIndex = 0;

	find ( 1, ARG, & setIndex );
	find ( 2, ARG, & setIndex );
	find ( 3, ARG, & setIndex );
	find ( 4, ARG, & setIndex );
	find ( 5, ARG, & setIndex );
	find ( 6, ARG, & setIndex );
	find ( 7, ARG, & setIndex );
	find ( 8, ARG, & setIndex );
	find ( 9, ARG, & setIndex );
	find ( 10, ARG, & setIndex );

	unionSet ( 0, 1, & set );
	unionSet ( 0, 8, & set );
	unionSet ( 8, 9, & set );
	unionSet ( 6, 7, & set );
	unionSet ( 2, 3, & set );
	unionSet ( 2, 5, & set );

	print ( set );
	freeSet ( set );
}


void testEdgeCases ( void ) {
	DisjointSet * set = NULL;
   
	for ( int i = 1; i <= 10; i ++ ) {
    	makeSet ( i, & set );
	}
    
	makeSet ( 5, & set );

	int setIndex = 0;

	find ( -1, ARG, & setIndex );
	find ( 0, ARG, & setIndex );
	find ( 100, ARG, & setIndex );

	unionSet ( -1, 1, & set );
	unionSet ( 1, -1, & set );
	unionSet ( -1, -1, & set );
	unionSet ( 1, 1, & set );

	print ( set );
	freeSet ( set );
}


void generated ( void ) {
	DisjointSet * set = NULL;
	for ( int i = 0; i < 10; i ++ ) {
		makeSet ( i, & set );
	}

	unionSet ( 9, 6, & set );
	unionSet ( 6, 8, & set );
	unionSet ( 7, 0, & set );
	unionSet ( 4, 4, & set );
	unionSet ( 1, 8, & set );
	unionSet ( 7, 7, & set );
	unionSet ( 1, 8, & set );
	unionSet ( 4, 9, & set );
	unionSet ( 8, 6, & set );
	unionSet ( 4, 5, & set );
	unionSet ( 3, 3, & set );
	unionSet ( 5, 3, & set );
	unionSet ( 9, 8, & set );
	unionSet ( 8, 2, & set );
	unionSet ( 9, 0, & set );
	unionSet ( 6, 4, & set );
	unionSet ( 0, 8, & set );
	unionSet ( 8, 0, & set );
	unionSet ( 8, 3, & set );
	unionSet ( 9, 0, & set );
	unionSet ( 5, 3, & set );
	unionSet ( 7, 6, & set );
	unionSet ( 6, 6, & set );
	unionSet ( 6, 0, & set );
	unionSet ( 7, 7, & set );
	unionSet ( 1, 1, & set );
	unionSet ( 6, 4, & set );
	unionSet ( 3, 7, & set );
	unionSet ( 0, 3, & set );
	unionSet ( 1, 7, & set );

	int value = 0;
	find ( 2, ARG, & value );
	find ( 5, ARG, & value );
	find ( 2, ARG, & value );
	find ( 2, ARG, & value );
	find ( 9, ARG, & value );
	find ( 1, ARG, & value );
	find ( 6, ARG, & value );
	find ( 6, ARG, & value );
	find ( 2, ARG, & value );
	find ( 4, ARG, & value );
	find ( 4, ARG, & value );
	find ( 9, ARG, & value );
	find ( 6, ARG, & value );
	find ( 7, ARG, & value );
	find ( 1, ARG, & value );
	find ( 9, ARG, & value );
	find ( 2, ARG, & value );
	find ( 4, ARG, & value );
	find ( 5, ARG, & value );
	find ( 7, ARG, & value );

	print ( set );
	freeSet ( set );
}

void fuzzed ( void ) {
	DisjointSet * set = NULL;
	for ( int i = 0; i < 10; i ++ ) {
		makeSet ( i, & set );
	}

	int value = 0;
	unionSet ( 6, 9, & set );
	find ( 3, ARG, & value );
	unionSet ( 0, 1, & set );
	unionSet ( 6, 2, & set );
	unionSet ( 1, 9, & set );
	unionSet ( 7, 7, & set );
	unionSet ( 8, 4, & set );
	find ( 7, ARG, & value );
	unionSet ( 8, 1, & set );
	unionSet ( 5, 7, & set );
	find ( 2, ARG, & value );
	find ( 0, ARG, & value );
	unionSet ( 2, 3, & set );
	unionSet ( 6, 5, & set );
	unionSet ( 4, 4, & set );
	unionSet ( 5, 2, & set );
	unionSet ( 8, 8, & set );
	unionSet ( 6, 5, & set );
	unionSet ( 8, 8, & set );
	unionSet ( 3, 0, & set );
	unionSet ( 6, 6, & set );
	unionSet ( 4, 9, & set );
	unionSet ( 4, 0, & set );
	unionSet ( 9, 5, & set );
	unionSet ( 2, 9, & set );

	print ( set );
	freeSet ( set );
}

#endif

int main ( void ) {
#ifdef INVALID
	printf ( "Invalid macro definition.\n" );
	printf ( "Specify one of the following:\n" );
	printf ( "BASIC, RANK, SIZE, COMPRESSION, SPLITTING, HALVING\n" );
#else
	testValid ( );
	testEdgeCases ( );
	generated ( );
	fuzzed ( );
#endif
	return 0;
}
