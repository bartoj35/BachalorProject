#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>


typedef struct TDisjointSet {
	int *	parents;
	int 	size;
} DisjointSet;



// create new disjoint set (allocate memory for the parents and initialize them
// checks for valid size parameter (non-negative integer)
// checks if set is not already allocated (would not cause overwriting of address => definite memory loss)
// param size - count of the elements in future disjoint set
// param set - pointer to the address of the disjoint set
// return	- true -> created valid set
//	 		- false -> could not create set
bool makeSet ( int size, DisjointSet ** set  ) {
	if ( ( * set ) == NULL ) {
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
					( * set ) = NULL;
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


// find the ID of the set to which the element belongs
// parent of the node is its granparent
// checks if elementIndex is valid (non-negative integer, in range of the set) 
// param elementIndex - index of the element, which setID we want to find
// param set - address of the disjoint set
// param setID - ID of the set to which the element belongs
// return	- true -> element with given index is in the set
//	 		- false -> element with given index is not in the set
bool find ( int elementIndex, DisjointSet ** set, int * setID ) {
	if ( set == NULL ) {
		printf ( "The element is not in set!\n" );
		return false;
	}
	else {
		if ( elementIndex >= 0 && elementIndex < ( * set ) -> size ) {
			* setID = elementIndex;
			
			while ( ( * setID ) != ( * set ) -> parents [ * setID ] ) {
				int tmp = * setId;
				* setID = ( * set ) -> parents [ * setId ];
				( * set ) -> parents [ tmp ] = ( * set ) -> parents [ * setID ];  
			}

			return true;
		}
		else {
			printf ( "Invalid element index!\n" );
			return false;
		}
	}
}


// union 2 sets in disjoint set into 1 set 
// checks if elementIndex1 and elementIndex2 is valid (non-negative integer, in range of the set) 
// param set - pointer to the address of the disjoint set
// return	- true -> successfull union of 2 sets 
//	 		- false -> element with given indexes is not in the set
bool unionSet ( int elementIndex1, int elementIndex2, DisjointSet ** set ) {
	if ( ( * set ) != NULL &&  elementIndex1 >= 0 && elementIndex1 < ( * set ) -> size && elementIndex2 >= 0 && elementIndex2 < ( * set ) -> size ) {
		int firstParent = 0, secondParent = 0;
		find ( elementIndex1, set, & firstParent );
		find ( elementIndex2, set, & secondParent );
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


// free allocated memory by given set
// param set - pointer to address of the set
void freeSet ( DisjointSet * set ) {
	if ( set != NULL ) {
		free ( set -> parents );
		set -> parents = NULL;
		set -> size = 0;
		free ( & ( * set ) );
	}
}


// print count of the elements in the disjoint set
// print parents of elements in given disjoint set
// param set - address of the disjoint set
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
       	makeSet ( 6, & set );

	unionSet ( 0, 1, & set );
	unionSet ( 2, 1, & set );
	unionSet ( 3, 4, & set );
        unionSet ( 4, 5, & set );
        unionSet ( 1, 5, & set );

	for ( int i = 0; i < 6; i ++ ) {
		int tmp = 0;
		find ( i, & set, & tmp );
	}

	printSet ( set );
	freeSet ( set );
	return 0;
}
