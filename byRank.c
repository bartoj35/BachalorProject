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

/*@ predicate freeable_set { L1 } ( DisjointSet * ds ) = (
  @ 	( 
  @			ds != \null && \valid ( ds ) 
  @		) ==> (
  @			\freeable { L1 } ( ds -> elements ) &&
  @			\freeable { L1 } ( ds -> parents ) && 
  @			\freeable { L1 } ( ds -> ranks )
  @		)
  @ );
*/

/*@ predicate valid_ranks ( DisjointSet * ds ) = (
  @ 	( 
  @			ds != \null && 
  @			\valid ( ds ) 
  @		) ==> (
  @			\forall integer index; 
  @				0 <= index < ds -> size ==> 
  @					ds -> ranks [ index ] <= ds -> ranks [ ds -> parents [ index ] ]
  @ 	)
  @ );
*/


/*@ predicate valid_parts ( DisjointSet * ds ) = (
  @		( 
  @			ds != \null && 
  @			\valid ( ds )  
  @		) ==> ( 
  @			ds -> size >= 1 &&
  @         ds -> capacity >= 1 && ds -> capacity >= ds -> size &&
  @			ds -> elements != \null && \valid ( ds -> elements + ( 0 .. ds -> capacity - 1 ) ) &&
  @			ds -> parents != \null && \valid ( ds -> parents + ( 0 .. ds -> capacity - 1 ) ) &&
  @			ds -> ranks != \null && \valid ( ds -> ranks + ( 0 .. ds -> capacity - 1 ) )
  @		)
  @ );		
*/

/*@ logic integer find { L1 } ( DisjointSet * ds, integer i, integer length ) = (
  @     ( length >= \at ( ds -> size, L1 ) ) 
  @     ? 
  @     -1 
  @     : 
  @     (   
  @         ( i == \at ( ds -> parents [ i ], L1 ) ) 
  @         ? 
  @         i 
  @         :
  @         find { L1 } ( ds, ds -> parents [ i ], length + 1 )
  @     ) 
  @ );
  @
  @ predicate correctly_unioned { L1, L2 } ( DisjointSet * ds, integer element1, integer element2 ) = (
  @     \forall integer i; 
  @         0 <= i < \at ( ds -> size, L2 ) ==> 
  @         (
  @             ( 
  @                 ( 
  @                     find { L1 } ( ds, i, 0 ) != find { L1 } (  ds, element1, 0 ) && 
  @                     find { L1 } ( ds, i, 0 ) != find { L1 } ( ds, element2, 0 ) 
  @                 ) ==> (
  @                     find { L1 } ( ds, i, 0 ) == find { L2 } ( ds, i, 0 ) 
  @                 )
  @             ) || ( 
  @                 find { L1 } ( ds, i, 0 ) == find { L2 } ( ds, element1, 0 ) && 
  @                 find { L2 } ( ds, i, 0 ) == find { L2 } ( ds, element2, 0 ) 
  @             )
  @         )
  @ );
  @
  @ predicate is_acyclic { L1 } ( DisjointSet * ds ) = (
  @     ds == \null || 
  @     ! \valid ( ds ) || 
  @     \forall integer i; 0 <= i < \at ( ds -> size, L1 ) ==> find ( ds, i, 0 ) != -1
  @ );
*/

/*@
  @ requires freeable_set { Here } ( set );
  @ requires valid_parts ( set );
  @	requires valid_ranks ( set );
  @ requires is_acyclic { Here } ( set );
  @  
  @ allocates \nothing;
  @
  @ assigns \nothing;
  @
  @ frees \nothing;
  @
  @ ensures \result == \true ==> \exists integer index; 0 <= index < set -> size ==> set -> elements [ index ] == element;
  @ ensures \result == \false ==> \forall integer index; 0 <= index < set -> size ==> set -> elements [ index ] != element;
  @
  @	ensures freeable_set { Here } ( set );
  @	ensures valid_parts ( set );
  @	ensures valid_ranks ( set );
  @ ensures is_acyclic { Here } ( set );
@*/
bool contains ( int element, DisjointSet * set ) {
    /*@
      @ loop invariant 0 <= i <= set -> size;
  	  @
      @ loop assigns i;
  	  @
      @ loop variant set -> size - i;
    @*/
    for ( int i = 0; i < set -> size; i ++ ) {
        if ( set -> elements [ i ] == element ) {
            return true;
        }
    }
    return false;
}


/*@
  @ requires set != \null;
  @ requires \valid ( set );
  @
  @ requires freeable_set { Here } ( * set );
  @ requires valid_parts ( * set );
  @	requires valid_ranks ( * set );
  @ requires is_acyclic { Here } ( * set );
  @
  @ behavior no_set:
  @		assumes * set == \null;
  @ 	assumes \allocable { Here } ( * set ); 
  @
  @		allocates * set;		
  @		allocates ( * set ) -> elements;		
  @		allocates ( * set ) -> parents;
  @		allocates ( * set ) -> ranks;
  @
  @		assigns * set;		
  @		
  @		frees \nothing;		
  @		
  @		ensures ( * set ) -> elements [ 0 ] == element;
  @		ensures ( * set ) -> parents [ 0 ] == 0;
  @		ensures ( * set ) -> ranks [ 0 ] == 0;
  @		ensures \result == 0;
  @
  @		ensures freeable_set { Here } ( * set );
  @ 	ensures valid_parts ( * set );
  @ 	ensures valid_ranks ( * set );
  @ 	ensures is_acyclic { Here } ( * set );
  @
  @ behavior resize_set:	
  @		assumes * set != \null;
  @		assumes \freeable { Here } ( * set );
  @		assumes ( * set ) -> size >= ( * set ) -> capacity; 
  @		assumes \forall integer index; 0 <= index < ( * set ) -> size ==> ( * set ) -> elements [ index ] != element;
  @		
  @		allocates * set;		
  @		allocates ( * set ) -> elements;		
  @		allocates ( * set ) -> parents;		
  @		allocates ( * set ) -> ranks;		
  @	
  @		assigns ( * set ) -> elements;	
  @		assigns ( * set ) -> elements [ 0 .. \old ( ( * set ) -> size ) ];	
  @		assigns ( * set ) -> parents;	
  @		assigns ( * set ) -> parents [ 0 .. \old ( ( * set ) -> size ) ];	
  @		assigns ( * set ) -> ranks;	
  @		assigns ( * set ) -> ranks [ 0 .. \old ( ( * set ) -> size ) ];	
  @		assigns ( * set ) -> capacity;	
  @		assigns ( * set ) -> size;	
  @	
  @		frees ( * set ) -> elements;		
  @		frees ( * set ) -> parents;		
  @	
  @		ensures ( * set ) -> elements [ \old ( ( * set ) -> size ) ] == element;
  @		ensures ( * set ) -> parents [ \old ( ( * set ) -> size ) ] == \old ( ( * set ) -> size );
  @		ensures ( * set ) -> ranks [ \old ( ( * set ) -> size ) ] == 0; 
  @		ensures \result == \old ( ( * set ) -> size );
  @
  @		ensures freeable_set { Here } ( * set );
  @ 	ensures valid_parts ( * set );
  @ 	ensures valid_ranks ( * set );
  @ 	ensures is_acyclic { Here } ( * set );
  @	
  @ behavior no_resize_set:	
  @		assumes * set != \null;
  @		assumes \freeable { Here } ( * set );
  @		assumes ( * set ) -> size < ( * set ) -> capacity; 
  @		assumes \forall integer index; 0 <= index < ( * set ) -> size ==> ( * set ) -> elements [ index ] != element;
  @		
  @		allocates \nothing;
  @
  @		assigns ( * set ) -> size;
  @		assigns ( * set ) -> elements [ \old ( ( * set ) -> size ) ];
  @		assigns ( * set ) -> parents [ \old ( ( * set ) -> size ) ];
  @		assigns ( * set ) -> ranks [ \old ( ( * set ) -> size ) ];
  @
  @		frees \nothing;
  @
  @		ensures ( * set ) -> elements [ \old ( ( * set ) -> size ) ] == element;
  @		ensures ( * set ) -> parents [ \old ( ( * set ) -> size ) ] == \old ( ( * set ) -> size );
  @		ensures ( * set ) -> ranks [ \old ( ( * set ) -> size ) ] == 0; 
  @		ensures \result == \old ( ( * set ) -> size );
  @
  @		ensures freeable_set { Here } ( * set );
  @ 	ensures valid_parts ( * set );
  @ 	ensures valid_ranks ( * set );
  @ 	ensures is_acyclic { Here } ( * set );
  @
  @ behavior in_set:	
  @		assumes * set != \null && \freeable { Here } ( * set );
  @		assumes \exists integer index; 0 <= index < ( * set ) -> size ==> ( * set ) -> elements [ index ] == element;
  @		
  @		allocates \nothing;
  @
  @		assigns \nothing;
  @
  @		frees \nothing;
  @
  @		ensures \result == -1;
  @
  @		ensures freeable_set { Here } ( * set );
  @		ensures valid_parts ( * set );
  @ 	ensures valid_ranks ( * set );
  @ 	ensures is_acyclic { Here } ( * set );
  @ 
  @ complete behaviors; 
*/
int makeSet ( int element, DisjointSet ** set  ) {
	if ( ( * set ) == NULL ) {
		* set = ( DisjointSet * ) malloc ( 1 * sizeof ( DisjointSet ) );
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
			printf ( "The element is already in set!\n" );
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


/*@
  @ requires freeable_set { Here } ( set );
  @	requires valid_parts ( set );
  @ requires valid_ranks ( set );
  @ requires is_acyclic { Here } ( set );
  @
  @ behavior valid:
  @     assumes 0 <= elementIndex < set -> size;
  @
  @     allocates \nothing;
  @
  @     assigns * setID;
  @
  @     frees \nothing;
  @
  @     ensures 0 <= * setID < set -> size;
  @     ensures set -> parents [ * setID ] == * setID;
  @     ensures \result == \true;
  @
  @		ensures freeable_set { Here } ( set );
  @ 	ensures valid_parts ( set );
  @ 	ensures valid_ranks ( set );
  @ 	ensures is_acyclic { Here } ( set );
  @
  @ behavior not_valid:
  @     assumes elementIndex < 0 || elementIndex >= set -> size;
  @ 
  @     allocates \nothing;
  @
  @     assigns \nothing;
  @
  @     frees \nothing;
  @ 
  @     ensures \result == \false;
  @
  @		ensures freeable_set { Here } ( set );
  @ 	ensures valid_parts ( set );
  @ 	ensures valid_ranks ( set );
  @ 	ensures is_acyclic { Here } ( set );
  @
@*/
bool find ( int elementIndex, DisjointSet * set, int * setID ) {
    if ( elementIndex >= 0 && elementIndex < set -> size ) {
        * setID = set -> parents [ elementIndex ];
        /*@
      	  @ loop invariant 0 <= * setID < set -> size;
		  @
      	  @ loop assigns * setID;
		  @
      	  @ loop variant set -> size - set -> ranks [ * setID ];
    	@*/
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

/*@
  @ behavior swap:
  @     assumes first != \null;
  @		assumes \valid ( first );
  @     assumes second != \null;
  @		assumes \valid ( second );
  @
  @     assigns * first;
  @     assigns * second;
  @
  @     ensures first != \null;
  @		ensures \valid ( first );
  @     ensures second != \null;
  @		ensures \valid ( second );
  @     ensures * first == \old ( * second ); 
  @     ensures * second == \old ( * first ); 
  @     ensures \result == \true;
  @
  @ behavior no_swap:
  @     assumes first == \null || ! \valid ( first ) || second == \null || ! \valid ( second );
  @
  @     ensures \result == \false;
  @
  @ disjoint behaviors;
  @ complete behaviors;
@*/
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

/*@
  @ requires set != \null;
  @ requires \valid ( set );
  @
  @	requires freeable_set { Here } ( * set );
  @	requires valid_parts ( * set );
  @ requires valid_ranks ( * set );
  @ requires is_acyclic { Here } ( * set );
  @
  @ behavior valid:
  @     assumes 0 <= elementIndex1 < ( * set ) -> size;
  @     assumes 0 <= elementIndex2 < ( * set ) -> size;
  @
  @     allocates \nothing;
  @
  @     
  @
  @     frees \nothing;
  @
  @     ensures \result == true;
  @
  @		ensures freeable_set { Here } ( * set );
  @		ensures valid_parts ( * set );
  @ 	ensures valid_ranks ( * set );
  @ 	ensures is_acyclic { Here } ( * set );
  @     
  @ behavior invalid_index:
  @     assumes ! ( 0 <= elementIndex1 < ( * set ) -> size ) || ! ( 0 <= elementIndex2 < ( * set ) -> size );
  @
  @     allocates \nothing;
  @
  @     assigns \nothing;
  @
  @     frees \nothing;
  @
  @     ensures \result == \false;
  @
  @		ensures freeable_set { Here } ( * set );
  @		ensures valid_parts ( * set );
  @ 	ensures valid_ranks ( * set );
  @ 	ensures is_acyclic { Here } ( * set );
  @ 	ensures correctly_unioned { Pre, Here } ( * set, elementIndex1, elementIndex2 );
  @ 
  @ disjoint behaviors; 
@*/
bool unionSet ( int elementIndex1, int elementIndex2, DisjointSet ** set ) {
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
		printf ( "Invalid index for first element!\n" );
	}

	if ( elementIndex2 < 0 || elementIndex2 >= ( * set ) -> size ) {
		printf ( "Invalid index for second element!\n" );
	}
	return false;
}

/*@
  @ requires freeable_set { Here } ( set );
  @ requires valid_parts ( set );
  @ requires valid_ranks ( set );
  @ requires is_acyclic { Here } ( set );
  @
  @ allocates \nothing;
  @
  @ assigns \nothing;
  @
  @ frees set;
  @ frees set -> elements;
  @ frees set -> parents;
  @ frees set -> ranks;
  @
  @ ensures \allocable { Here } ( set );
@*/
void freeSet ( DisjointSet * set ) {
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

/*@
  @ requires \true;
  @
  @ allocates \nothing;
  @
  @ assigns \nothing;
  @
  @ frees \nothing;
  @
  @ ensures \result == 0;
*/
int main ( void ) {
	DisjointSet * set = NULL;
	// test adding new element
    makeSet ( 1, & set );

	// test adding new element with capacity
    makeSet ( 2, & set );

	// test adding new element with resize
    makeSet ( 3, & set );
    makeSet ( 4, & set );
    makeSet ( 5, & set );
    makeSet ( 6, & set );

    // test adding element that is already in set
 	makeSet ( 6, & set );
	
	int value = 0;
	// find element on valid index
	find ( 1, set, & value );
	
	// find element on negative index
	find ( -333, set, & value );
	
	// find element on too large index
	find ( 10, set, & value );

	// test union	
	unionSet ( 0, 1, & set );
	unionSet ( 2, 3, & set );
	unionSet ( 1, 3, & set );
	
	// test union of larger set to smaller
	unionSet ( 0, 5, & set );
	

	// test union of same sets
	unionSet ( 0, 0, & set );
	
	// test union negative left set index
	unionSet ( -1, 0, & set );
	
	// test union too large left set index
	unionSet ( 10, 0, & set );
	
	// test union negative right set index
	unionSet ( 0, -1, & set );

	// test union too large left set index
	unionSet ( 0, 10, & set );

	// test swap
   	int a = 1, b = 2;
	swap ( & a, & b );
	swap ( NULL, & b );
	swap ( & a, NULL );
	swap ( NULL, NULL );
	
	// test free
	freeSet ( set );
	//@ assert 0 == 1;
	return 0;
}
