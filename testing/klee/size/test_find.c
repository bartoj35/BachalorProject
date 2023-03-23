#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#define DEFAULT_CAPACITY 2


typedef struct TUnionFind {
	int *	parents;
	int * elements;
	int *	sizes;
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
		( * set ) -> elements = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> elements ) );
		( * set ) -> parents = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> parents ) );
		( * set ) -> sizes = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> sizes ) );

		( * set ) -> elements [ 0 ] = element;
		( * set ) -> parents [ 0 ] = 0;
		( * set ) -> sizes [ 0 ] = 1;
		return ( * set ) -> size - 1;
	}
	else {
		if ( contains ( element, * set ) == true ) {
			printf ( "The element is already in set!\n" );
			return -1;
		}

		if ( ( * set ) -> capacity == ( * set ) -> size ) {
			( * set ) -> capacity *= 2;
			( * set ) -> size ++;
			( * set ) -> elements = ( int * ) realloc ( ( * set ) -> elements, ( * set ) -> capacity * sizeof ( * ( * set ) -> elements ) );	
			( * set ) -> parents = ( int * ) realloc ( ( * set ) -> parents, ( * set ) -> capacity * sizeof ( * ( * set ) -> parents ) );	
			( * set ) -> sizes = ( int * ) realloc ( ( * set ) -> sizes, ( * set ) -> capacity * sizeof ( * ( * set ) -> sizes ) );	
			
			( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
			( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
			( * set ) -> sizes [ ( *set ) -> size - 1 ] = 1;
			return ( * set ) -> size - 1;
		}
		else {
			( * set ) -> size ++;
			( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
			( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
			( * set ) -> sizes [ ( *set ) -> size - 1 ] = 1;
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
    	printf ( "Invalid element index!\n" );
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

		if ( ( * set ) -> sizes [ firstParent ] > ( * set ) -> sizes [ secondParent ] ) {
			swap ( & firstParent, & secondParent );
		}

		( * set ) -> parents [ firstParent ] = secondParent;
		( * set ) -> sizes [ secondParent ] += ( * set ) -> sizes [ firstParent ];
		return true;
	}

	if ( elementIndex1 < 0 || elementIndex1 >= ( * set ) -> size ) {
		printf ( "Invalid index for first element!\n" );
	}
	
	if ( elementIndex2 < 0 || elementIndex2 >= ( * set ) -> size ) {
		printf ( "Invalid index for second element!\n" );
	}
	return false;
}


void freeSet ( UnionFind * set ) {
	free ( set -> sizes );
	set -> sizes = NULL;
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
    	printf ( "%d: %d, size %d\n", i, set -> parents [ i ], set -> sizes [ i ] );
    }
}


int main ( void ) {
    UnionFind * set = NULL;

    for ( int i = 1; i <= 6; i ++ ) {
        makeSet ( i, & set );
    }

    int value = 0;
    unionSet ( 0, 1, & set );
    unionSet ( 1, 2, & set );

    int a;
    klee_make_symbolic ( & a, sizeof ( a ), "a" );
    find ( a, set, & value );

    freeSet ( set );
    return 0;
}

