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
	test1 ( );
	test2 ( );
#endif
	return 0;
}
