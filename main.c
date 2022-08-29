#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>


typedef struct TDisjointSet {
	int *	parents;
	int 	size;
} DisjointSet;


bool makeSet ( int size, DisjointSet ** set  ) {
	if ( * set == NULL ) {
		if ( size > 0 ) {
			* set = ( DisjointSet * ) malloc ( 1 * sizeof ( DisjointSet ) );
			if ( * set != NULL ) {
				( * set ) -> size = size;
				( * set ) -> parents = ( int * ) malloc ( ( ( * set ) -> size ) * sizeof ( ( * set ) -> parents ) );		// parentheses around resultSet . size are just to increase readablity
				if ( ( * set ) -> parents != NULL ) {
					for ( int i = 0; i < ( * set ) -> size; i ++ ) {
						( * set ) -> parents [ i ] = i;
					}
					return true;
				}
				else {
					printf ( "Could not allocate part of set!\n" );
					free ( * set );
					* set = NULL;
					return false;
				}
			}
			else {
				printf ( "Could not allocate set!\n" );
				return false;
			}
		}
		else if ( size == 0 ) {
			return true;
		}
		else {
			printf ( "Invalid set size!\n" );
			return false;
		}
	}
	else {
		printf ( "Set already exists!\n" );
		return false;
	}
}


bool find ( int elementIndex, DisjointSet * set, int * setID ) {
	if ( set == NULL ) {
		printf ( "The element is not in set!\n" );
		return false;
	}
	else {
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
}
	
bool unionSet ( int elementIndex1, int elementIndex2, DisjointSet ** set ) {
	if ( ( * set ) != NULL &&  elementIndex1 >= 0 && elementIndex1 < ( * set ) -> size && elementIndex2 >= 0 && elementIndex2 < ( * set ) -> size ) {
		int firstParent = 0, secondParent = 0;
		find ( elementIndex1, * set, & firstParent );
		find ( elementIndex2, * set, & secondParent );
		( * set ) -> parents [ secondParent ] = firstParent;
		return true;
	}
	else if ( ( * set ) == NULL ) {
		printf ( "Can't union elements of empty set!\n" );
		return false;
	}
	else if ( elementIndex1 >= 0 || elementIndex1 <= ( * set ) -> size ) {
		printf ( "Invalid index for first element!\n" );
		return false;
	}
	else {
		printf ( "Invalid index for second element!\n" );
		return false;
	}
}


void freeSet ( DisjointSet ** set ) {
	if ( ( * set ) != NULL ) {
		free ( ( * set ) -> parents );
		( * set ) -> parents = NULL;
		( * set ) -> size = 0;
		free ( * set );
	}
}


void printSet ( DisjointSet * set ) {
	if ( set != NULL ) {
		printf ( "Size of the set is: %d\n", set -> size );
	}
	printf ( "{ " );	
	if ( set != NULL ) {
		for ( int i = 0; i < set -> size; i ++ ) {\
			printf ( "%d", set -> parents [ i ] );
			if ( i != set -> size - 1 ) { 
				printf ( ", " );\
			}
		} 
	}
	printf ( " }\n" );
}


int main ( ) {
	DisjointSet * set = NULL;
	makeSet ( 5, & set );

	for ( int i = 0; i < 5; i ++ ) {
		int parent = 0;
		find ( i, set, & parent );
		printf ( "%d's parent is: %d\n", i, parent ); 
		printSet ( set );
		printf ( "\n\n" );
	}
	
	for ( int i = 0; i < 4; i ++ ) {
		unionSet ( i, i + 1, & set );
		int parent = 0;
		find ( i, set, & parent );
		printf ( "%d union %d:\t%d's parent is: %d\n", i, i + 1, i, parent ); 
		printSet ( set );
		printf ( "\n\n" );
	}

	printSet ( set );
	freeSet ( & set );
	return 0;
}
