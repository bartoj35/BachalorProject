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
	

void freeSet ( DisjointSet ** set ) {
	if ( ( * set ) != NULL ) {
		free ( ( * set ) -> parents );
		( * set ) -> parents = NULL;
		( * set ) -> size = 0;
		free ( * set );
	}
}


int main ( ) {
	DisjointSet * set = NULL;
	makeSet ( 5, & set ); 
	freeSet ( & set );
	return 0;
}
