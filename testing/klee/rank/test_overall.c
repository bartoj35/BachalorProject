#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>


#define DEFAULT_CAPACITY 2


typedef struct TUnionFind {
	int *	ranks;
	int *	parents;
	int *	elements;
	int 	capacity;
	int 	size;
} UnionFind;


bool contains ( int element, UnionFind * set ) {
    for ( int i = 0; i < set -> size; i ++ ) {
    	if ( set -> elements [ i ] == element ) {
        	return true;
    	}
    }
    return false;
}


int makeSet ( int element, UnionFind ** set  ) {
	if ( ( * set ) == NULL ) {
		* set = ( UnionFind * ) malloc ( 1 * sizeof ( UnionFind ) );
		( * set ) -> size = 1;
		( * set ) -> capacity = DEFAULT_CAPACITY;
		( * set ) -> elements = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( ( * set ) -> elements ) );
		( * set ) -> parents = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( ( * set ) -> parents ) );
		( * set ) -> ranks = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( ( * set ) -> ranks ) );
		( * set ) -> elements [ 0 ] = element;
		( * set ) -> parents [ 0 ] = 0;
		( * set ) -> ranks [ 0 ] = 0;
		return ( * set ) -> size - 1;
	}
	else {
		if ( contains ( element, * set ) == true ) {
			fprintf ( stderr, "The element is already in set!\n" );
			return -1;
		}

		if ( ( * set ) -> capacity == ( * set ) -> size ) {
			( * set ) -> capacity *= 2;
			( * set ) -> size ++;
			( * set ) -> elements = ( int * ) realloc ( ( * set ) -> elements, ( * set ) -> capacity * sizeof ( * ( * set ) -> elements ) );	
			( * set ) -> parents = ( int * ) realloc ( ( * set ) -> parents, ( * set ) -> capacity * sizeof ( * ( * set ) -> parents ) );	
			( * set ) -> ranks = ( int * ) realloc ( ( * set ) -> ranks, ( * set ) -> capacity * sizeof ( * ( * set ) -> ranks ) );	
			
			( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
			( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
			( * set ) -> ranks [ ( *set ) -> size - 1 ] = 0;
			return ( * set ) -> size - 1;
		}
		else {
			( * set ) -> size ++;
			( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
			( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
			( * set ) -> ranks [ ( *set ) -> size - 1 ] = 0;
			return ( * set ) -> size - 1;
		}
	}
}


bool find ( int elementIndex, UnionFind * set, int * setID ) {
    if ( elementIndex >= 0 && elementIndex < set -> size ) {
    * setID = set -> parents [ elementIndex ];
		while ( ( * setID ) != set -> parents [ * setID ] ) {
        * setID = set -> parents [ * setID ];
    }
    return true;
    }
    else {
    	fprintf ( stderr, "Invalid element index!\n" );
    	return false;
    }
}


bool swap ( int * first, int * second ) {
	if ( first != NULL && second != NULL ) {
		int tmp = * first;
		* first = * second;
		* second = tmp;
		return true;
	}
	else {
		return false;
	}
}


bool unionSet ( int elementIndex1, int elementIndex2, UnionFind ** set ) {
	if ( elementIndex1 >= 0 && elementIndex1 < ( * set ) -> size && elementIndex2 >= 0 && elementIndex2 < ( * set ) -> size ) {
		int firstParent = 0, secondParent = 0;
		find ( elementIndex1, * set, & firstParent );
		find ( elementIndex2, * set, & secondParent );

		if ( firstParent == secondParent ) {
			return true;
		}

		if ( ( * set ) -> ranks [ firstParent ] > ( * set ) -> ranks [ secondParent ] ) {
			swap ( & firstParent, & secondParent );
		}

		( * set ) -> parents [ firstParent ] = secondParent;
		if ( ( * set ) -> ranks [ firstParent ] == ( * set ) -> ranks [ secondParent ] ) {
			( * set ) -> ranks [ secondParent ] ++;
		}
		return true;
	}
	
	if ( elementIndex1 < 0 || elementIndex1 >= ( * set ) -> size ) {
		fprintf ( stderr, "Invalid index for first element!\n" );
	}

	if ( elementIndex2 < 0 || elementIndex2 >= ( * set ) -> size ) {
		fprintf ( stderr, "Invalid index for second element!\n" );
	}
	return false;
}


void freeSet ( UnionFind * set ) {
	free ( set -> ranks );
	set -> ranks = NULL;
	free ( set -> parents );
	set -> parents = NULL;
	free ( set -> elements );
	set -> elements = NULL;
	set -> size = 0;
	set -> capacity = 0;
	free ( & ( * set ) );
}


void print ( UnionFind * set ) {
    for ( int i = 0; i < set -> size; i ++ ) {
    	printf ( "%d: %d, rank %d\n", i, set -> parents [ i ], set -> ranks [ i ] );
    }
}


int main ( void ) {
    UnionFind * set = NULL;

    for ( int i = 1; i <= 6; i ++ ) {
        makeSet ( i, & set );
    }

    int a;
    klee_make_symbolic ( & a, sizeof ( a ), "a" );
    makeSet ( a, & set );

    int b;
    klee_make_symbolic ( & b, sizeof ( b ), "b" );
    int value = 0;
    find ( b, & set, & value );

    int c, d;
    klee_make_symbolic ( & c, sizeof ( c ), "c" );
    klee_make_symbolic ( & d, sizeof ( d ), "d" );

    unionSet ( c, d, & set );

    int e;
    klee_make_symbolic ( & e, sizeof ( e ), "e" );
    find ( e, & set, & value );

    freeSet ( set );
    return 0;
}


