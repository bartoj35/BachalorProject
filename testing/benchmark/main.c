#include <stdio.h>


#if defined ( BASIC )
	#include "basic.h"
#elif defined ( RANK )
	#include "rank.h"
#elif defined ( SIZE )
	#include "size.h"
#elif defined ( COMPRESSION )
	#include "compression.h"
#elif defined ( HALVING )
	#include "halving.h"
#elif defined ( SPLITTING )
	#include "splitting.h"
#else
	#define INVALID
#endif


#ifndef INVALID
void testValid ( void ) {
	UnionFind * set = NULL;

	for ( int i = 1; i <= 10; i ++ ) {
    	makeSet ( i, & set );
	}

	find ( 1, set );
	find ( 2, set );
	find ( 3, set );
	find ( 4, set );
	find ( 5, set );
	find ( 6, set );
	find ( 7, set );
	find ( 8, set );
	find ( 9, set );
	find ( 10, set );

	unionSet ( 0, 1, set );
	unionSet ( 0, 8, set );
	unionSet ( 8, 9, set );
	unionSet ( 6, 7, set );
	unionSet ( 2, 3, set );
	unionSet ( 2, 5, set );

	print ( set );
	freeSet ( set );
}


void testEdgeCases ( void ) {
	UnionFind * set = NULL;
   
	for ( int i = 1; i <= 10; i ++ ) {
    	makeSet ( i, & set );
	}
    
	makeSet ( 5, & set );

	find ( -1, set );
	find ( 0, set );
	find ( 100, set );

	unionSet ( -1, 1, set );
	unionSet ( 1, -1, set );
	unionSet ( -1, -1, set );
	unionSet ( 1, 1, set );

	print ( set );
	freeSet ( set );
}


void generated ( void ) {
	UnionFind * set = NULL;
	for ( int i = 0; i < 10; i ++ ) {
		makeSet ( i, & set );
	}

	unionSet ( 9, 6, set );
	unionSet ( 6, 8, set );
	unionSet ( 7, 0, set );
	unionSet ( 4, 4, set );
	unionSet ( 1, 8, set );
	unionSet ( 7, 7, set );
	unionSet ( 1, 8, set );
	unionSet ( 4, 9, set );
	unionSet ( 8, 6, set );
	unionSet ( 4, 5, set );
	unionSet ( 3, 3, set );
	unionSet ( 5, 3, set );
	unionSet ( 9, 8, set );
	unionSet ( 8, 2, set );
	unionSet ( 9, 0, set );
	unionSet ( 6, 4, set );
	unionSet ( 0, 8, set );
	unionSet ( 8, 0, set );
	unionSet ( 8, 3, set );
	unionSet ( 9, 0, set );
	unionSet ( 5, 3, set );
	unionSet ( 7, 6, set );
	unionSet ( 6, 6, set );
	unionSet ( 6, 0, set );
	unionSet ( 7, 7, set );
	unionSet ( 1, 1, set );
	unionSet ( 6, 4, set );
	unionSet ( 3, 7, set );
	unionSet ( 0, 3, set );
	unionSet ( 1, 7, set );

	find ( 2, set );
	find ( 5, set );
	find ( 2, set );
	find ( 2, set );
	find ( 9, set );
	find ( 1, set );
	find ( 6, set );
	find ( 6, set );
	find ( 2, set );
	find ( 4, set );
	find ( 4, set );
	find ( 9, set );
	find ( 6, set );
	find ( 7, set );
	find ( 1, set );
	find ( 9, set );
	find ( 2, set );
	find ( 4, set );
	find ( 5, set );
	find ( 7, set );

	print ( set );
	freeSet ( set );
}

void fuzzed ( void ) {
	UnionFind * set = NULL;
	for ( int i = 0; i < 10; i ++ ) {
		makeSet ( i, & set );
	}

	unionSet ( 6, 9, set );
	find ( 3, set );
	unionSet ( 0, 1, set );
	unionSet ( 6, 2, set );
	unionSet ( 1, 9, set );
	unionSet ( 7, 7, set );
	unionSet ( 8, 4, set );
	find ( 7, set );
	unionSet ( 8, 1, set );
	unionSet ( 5, 7, set );
	find ( 2, set );
	find ( 0, set );
	unionSet ( 2, 3, set );
	unionSet ( 6, 5, set );
	unionSet ( 4, 4, set );
	unionSet ( 5, 2, set );
	unionSet ( 8, 8, set );
	unionSet ( 6, 5, set );
	unionSet ( 8, 8, set );
	unionSet ( 3, 0, set );
	unionSet ( 6, 6, set );
	unionSet ( 4, 9, set );
	unionSet ( 4, 0, set );
	unionSet ( 9, 5, set );
	unionSet ( 2, 9, set );

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
