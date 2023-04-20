#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>


#define DEFAULT_CAPACITY 2


typedef struct TUnionFind {
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
        ( * set ) -> elements = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> elements ) );
        ( * set ) -> parents = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( * ( * set ) -> parents ) );
        ( * set ) -> elements [ 0 ] = element;
        ( * set ) -> parents [ 0 ] = 0;
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


int find ( int elementIndex, UnionFind * set ) {
	if ( elementIndex >= 0 && elementIndex < set -> size ) {
		int id = elementIndex;
		
		while ( id != set -> parents [ id ] ) {
			int tmp = id;
			id = set -> parents [ id ];
			set -> parents [ tmp ] = set -> parents [ id ];  
		}

		return id;
	}
	else {
		fprintf ( stderr, "Invalid element index!\n" );
		return -1;
	}
}


bool unionSet ( int elementIndex1, int elementIndex2, UnionFind * set ) {
    int firstParent = find ( elementIndex1, set );
    int secondParent = find ( elementIndex2, set );

    if ( firstParent == -1 || secondParent == -1 ) {
        if ( firstParent == -1 ) {
            fprintf ( stderr, "Invalid index for first element!\n" );
        }
        if ( secondParent == -1 ) {
            fprintf ( stderr, "Invalid index for second element!\n" );
        }
        return false;
    }
	
	if ( firstParent == secondParent ) {
		return true;
	}	       
		
	set -> parents [ secondParent ] = elementIndex1;
	return true;
}


void freeSet ( UnionFind * set ) {
    free ( set -> parents );
    set -> parents = NULL;
    free ( set -> elements );
    set -> elements = NULL;
    set -> size = 0;
    set -> capacity = 0;
    free ( & ( * set ) );
    set = NULL;
}


void print ( UnionFind * set ) {
	for ( int i = 0; i < set -> size; i ++ ) {
		printf ( "%d: %d\n", i, set -> parents [ i ] ); 
	}
}


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


int main ( void ) {
	testValid ( );
	testEdgeCases ( );
	return 0;
}
