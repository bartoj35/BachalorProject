#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#define DEFAULT_CAPACITY 2


typedef struct TDisjointSet {
	int *	ranks;
	int *	parents;
	int *	elements;
	int 	capacity;
	int 	size;
} DisjointSet;



// create new disjoint set (allocate memory for the parents and initialize them
// checks for valid size parameter (non-negative integer)
// checks if set is not already allocated (would not cause overwriting of address => definite memory loss)
// param size - count of the elements in future disjoint set
// param set - pointer to the address of the disjoint set
// return	- non-negative number -> index of inserted element
//	 	- -1 -> could not insert element
bool makeSet ( int element, DisjointSet ** set  ) {
	if ( ( * set ) == NULL ) {
		* set = ( DisjointSet * ) malloc ( 1 * sizeof ( DisjointSet ) );
		if ( * set != NULL ) {
			( * set ) -> size = 1;
			( * set ) -> capacity = DEFAULT_CAPACITY;
			( * set ) -> parents = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( ( * set ) -> parents ) );
			( * set ) -> elements = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( ( * set ) -> elements ) );
			( * set ) -> ranks = ( int * ) malloc ( DEFAULT_CAPACITY * sizeof ( ( * set ) -> ranks ) );

			if ( ( * set ) -> parents != NULL && ( * set ) -> elements != NULL && ( * set ) -> ranks != NULL ) {
				( * set ) -> parents [ 0 ] = 0;
				( * set ) -> elements [ 0 ] = element;
				( * set ) -> ranks [ 0 ] = 0;
				return ( * set ) -> size - 1;
			}
			else {
				if ( ( * set ) -> parents != NULL ) {
					free ( ( * set ) -> parents );
					( * set ) -> parents = NULL;
				}
				else {
					printf ( "Could not allocate parents\n" );
				}
			
				if ( ( * set ) -> elements != NULL ) {
					free ( ( * set ) -> elements );
					( * set ) -> elements = NULL;
				}
				else {
					printf ( "Could not allocate elements\n" );
				}

				if ( ( * set ) -> ranks != NULL ) {
						free ( ( * set ) -> ranks );
						( * set ) -> ranks = NULL;
					}
					else {
						printf ( "Could not allocate ranks\n" );
					}

				( * set ) -> capacity = 0;
				( * set ) -> size = 0;
				free ( * set );
				( * set ) = NULL;
				return -1;
			}
		}
		else {
			printf ( "Could not allocate set!\n" );
			return -1;
		}
	}
	else {
		if ( ( * set ) -> capacity == ( * set ) -> size ) {
			( * set ) -> capacity *= 2;
			( * set ) -> elements = ( int * ) realloc ( ( * set ) -> elements, ( * set ) -> capacity * sizeof ( * ( * set ) -> elements ) );	
			( * set ) -> parents = ( int * ) realloc ( ( * set ) -> parents, ( * set ) -> capacity * sizeof ( * ( * set ) -> parents ) );	
			( * set ) -> ranks = ( int * ) realloc ( ( * set ) -> ranks, ( * set ) -> capacity * sizeof ( * ( * set ) -> ranks ) );	
			
			if ( ( * set ) -> parents != NULL && ( * set ) -> elements != NULL && ( * set ) -> ranks != NULL ) {
				( * set ) -> size ++;
				( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
				( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
				( * set ) -> ranks [ ( *set ) -> size - 1 ] = 0;
				return ( * set ) -> size - 1;
			}
			else {
				if ( ( * set ) -> parents != NULL && ( * set ) -> elements != NULL ) {
					( * set ) -> parents [ 0 ] = 0;
					( * set ) -> elements [ 0 ] = element;
					return ( * set ) -> size - 1;
				}
				else {
					if ( ( * set ) -> parents != NULL ) {
						free ( ( * set ) -> parents );
						( * set ) -> parents = NULL;
					}
					else {
						printf ( "Could not allocate parents\n" );
					}
			
					if ( ( * set ) -> elements != NULL ) {
						free ( ( * set ) -> elements );
						( * set ) -> elements = NULL;
					}
					else {
						printf ( "Could not allocate elements\n" );
					}

					if ( ( * set ) -> ranks != NULL ) {
						free ( ( * set ) -> ranks );
						( * set ) -> ranks = NULL;
					}
					else {
						printf ( "Could not allocate ranks\n" );
					}

					( * set ) -> capacity = 0;
					( * set ) -> size = 0;
					free ( * set );
					( * set ) = NULL;
					return -1;
				}
			}
		}
		else {
			( * set ) -> size ++; 	
			( * set ) -> parents [ ( *set ) -> size - 1 ] = ( *set ) -> size - 1;
			( * set ) -> elements [ ( *set ) -> size - 1 ] = element;
			( * set ) -> ranks [ ( *set ) -> size - 1 ] = 0;
			return ( * set ) -> size - 1;
		}
	}
}



// find the ID of the set to which the element belongs
// checks if elementIndex is valid (non-negative integer, in range of the set) 
// param elementIndex - index of the element, which setID we want to find
// param set - address of the disjoint set
// param setID - ID of the set to which the element belongs
// return	- true -> element with given index is in the set
//	 		- false -> element with given index is not in the set
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


// swap 2 integers
// check if both pointers to integers are valid
// param first - pointer to first integer
// param second - pointer to second integer
// return true 	- swap successful (both pointers were valid)
// 	  false - swap failed (some invalid pointer)
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


// union 2 sets in disjoint set into 1 set 
// checks if elementIndex1 and elementIndex2 is valid (non-negative integer, in range of the set) 
// param set - pointer to the address of the disjoint set
// return	- true -> successfull union of 2 sets 
//	 		- false -> element with given indexes is not in the set
bool unionSet ( int elementIndex1, int elementIndex2, DisjointSet ** set ) {
	if ( ( * set ) != NULL &&  elementIndex1 >= 0 && elementIndex1 < ( * set ) -> size && elementIndex2 >= 0 && elementIndex2 < ( * set ) -> size ) {
		int firstParent = 0, secondParent = 0;
		find ( elementIndex1, * set, & firstParent );
		find ( elementIndex2, * set, & secondParent );

		if ( firstParent == secondParent ) {
			printf ( "Elements are in the same set!\n" );
			return false;
		}

		if ( ( * set ) -> ranks [ firstParent ] > ( * set ) -> ranks [ secondParent ] ) {
			if ( swap ( & firstParent, & secondParent ) == false ) {
				printf ( "Could not swap 2 integers!\n" );
				return false;
			}
		}

		( * set ) -> parents [ firstParent ] = secondParent;
		if ( ( * set ) -> ranks [ firstParent ] == ( * set ) -> ranks [ secondParent ] ) {
			( * set ) -> ranks [ secondParent ] ++;
		}
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
}


void printArray ( int * arr, int size ) {
	printf ( "{ " );	
	for ( int i = 0; i < size; i ++ ) {\
		printf ( "%d", arr [ i ] );
		if ( i != size - 1 ) { 
			printf ( ", " );\
		}
	} 
	printf ( " }\n" );
}	

// print count of the elements in the disjoint set
// print parents of elements in given disjoint set
// param set - address of the disjoint set
void printSet ( DisjointSet * set ) {
	if ( set != NULL ) {
		printf ( "Size of the set is: %d\n", set -> size );
	}
	
	if ( set != NULL ) {
		printf ( "Parents: " );
		printArray ( set -> parents, set -> size );	
		printf ( "Ranks: " );
		printArray ( set -> ranks, set -> size );	
	}
}


int main ( ) {
	DisjointSet * set = NULL;
	for ( int i = 0; i < 6; i ++ ) {
		makeSet ( i, & set );
	}


	unionSet ( 0, 1, & set ); 
	unionSet ( 2, 1, & set ); 
	unionSet ( 3, 4, & set ); 
	unionSet ( 4, 5, & set ); 
	unionSet ( 1, 5, & set ); 

	printSet ( set );
	freeSet ( set );
	return 0;
}
