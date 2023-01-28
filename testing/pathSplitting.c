#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>


#define DEFAULT_CAPACITY 2


typedef struct TDisjointSet {
	int *	parents;
	int *	elements;
	int 	capacity;
	int 	size;
} DisjointSet;


bool contains ( int element, DisjointSet * set ) {
    for ( int i = 0; i < set -> size; i ++ ) {
        if ( set -> elements [ i ] == element ) {
            return true;
        }
    }
    return false;
}


int makeSet ( int element, DisjointSet ** set  ) {
    if ( ( * set ) == NULL ) {
        * set = ( DisjointSet * ) malloc ( 1 * sizeof ( DisjointSet ) );
        ( * set ) -> size = 1;
        ( * set ) -> capacity = DEFAULT_CAPACITY;
        ( * set ) -> elements = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> elements ) );
        ( * set ) -> parents = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> parents ) );
        ( * set ) -> elements [ 0 ] = element;
        ( * set ) -> parents [ 0 ] = 0;
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

            ( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
            ( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
            return ( * set ) -> size - 1;
        }
        else {
            ( * set ) -> size ++;
            ( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
            ( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
            return ( * set ) -> size - 1;
        }
    }
}


bool find ( int elementIndex, DisjointSet ** set, int * setID ) {
	if ( elementIndex >= 0 && elementIndex < ( * set ) -> size ) {
		* setID = elementIndex;
		
		while ( ( * setID ) != ( * set ) -> parents [ * setID ] ) {
			int tmp = * setID;
			* setID = ( * set ) -> parents [ * setID ];
			( * set ) -> parents [ tmp ] = ( * set ) -> parents [ * setID ];  
		}

		return true;
	}
	else {
		printf ( "Invalid element index!\n" );
		return false;
	}
}


bool unionSet ( int elementIndex1, int elementIndex2, DisjointSet ** set ) {
	if ( elementIndex1 >= 0 && elementIndex1 < ( * set ) -> size && elementIndex2 >= 0 && elementIndex2 < ( * set ) -> size ) {
		int firstParent = 0, secondParent = 0;
		find ( elementIndex1, set, & firstParent );
		find ( elementIndex2, set, & secondParent );
		
		if ( firstParent == secondParent ) {
			return true;
		}	       
		
		( * set ) -> parents [ secondParent ] = elementIndex1;
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


void freeSet ( DisjointSet * set ) {
    free ( set -> parents );
    set -> parents = NULL;
    free ( set -> elements );
    set -> elements = NULL;
    set -> size = 0;
    set -> capacity = 0;
    free ( & ( * set ) );
    set = NULL;
}


void print ( DisjointSet * set ) {
    for ( int i = 0; i < set -> size; i ++ ) {
        printf ( "%d: %d\n", i, set -> parents [ i ] );
    }
}


void testValid ( void ) {
    DisjointSet * set = NULL;

    for ( int i = 1; i <= 10; i ++ ) {
        makeSet ( i, & set );
    }

    int setIndex = 0;

    find ( 1, & set, & setIndex );
    find ( 2, & set, & setIndex );
    find ( 3, & set, & setIndex );
    find ( 4, & set, & setIndex );
    find ( 5, & set, & setIndex );
    find ( 6, & set, & setIndex );
    find ( 7, & set, & setIndex );
    find ( 8, & set, & setIndex );
    find ( 9, & set, & setIndex );
    find ( 10, & set, & setIndex );

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

    find ( -1, & set, & setIndex );
    find ( 0, & set, & setIndex );
    find ( 100, & set, & setIndex );

    unionSet ( -1, 1, & set );
    unionSet ( 1, -1, & set );
    unionSet ( -1, -1, & set );
    unionSet ( 1, 1, & set );

    print ( set );

    freeSet ( set );
}


int main ( void ) {
    testValid ( );
    testEdgeCases ( );
    return 0;
}
