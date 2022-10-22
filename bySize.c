#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>

#define DEFAULT_CAPACITY 2


typedef struct TDisjointSet {
	int *	parents;
	int * elements;
	int *	sizes;
	int 	capacity;
	int 	size;
} DisjointSet;

//@ predicate valid_sizes ( DisjointSet * ds ) = ds != \null ==> \forall integer index; 0 <= index < ds -> size ==> ds -> sizes [ index ] <= ds -> sizes [ ds -> parents [ index ] ];

/*@ predicate freeable_set { L1 } ( DisjointSet * ds ) =
        ( ds != \null && \valid ( ds ) ) ==>
        (
            \freeable { L1 } ( ds -> elements ) &&
            \freeable { L1 } ( ds -> parents ) && 
            \freeable { L1 } ( ds -> sizes )
        );
*/

/*@ predicate valid_parts { L1 } ( DisjointSet * ds ) =
        ( ds != \null && \valid ( ds ) ) ==>
        (
            ds -> size >= 1 &&
            ds -> capacity >= 1 && ds -> capacity >= ds -> size &&
            ds -> elements != \null && \valid ( ds -> elements + ( 0 .. ds -> capacity - 1 ) ) &&
            ds -> parents != \null && \valid ( ds -> parents + ( 0 .. ds -> capacity - 1 ) ) &&
            ds -> sizes != \null && \valid ( ds -> sizes + ( 0 .. ds -> capacity - 1 ) )
        );      
*/

/*@
  @ requires freeable_set ( set );
  @ requires valid_parts ( set );
  @ requires valid_sizes ( set );
  @  
  @ allocates \nothing;
  @
  @ assigns \nothing;
  @
  @ frees \nothing;
  @
  @ ensures freeable_set ( set );
  @ ensures valid_parts ( set );
  @ ensures valid_sizes ( set );
  @ ensures \result == \true ==> ( \exists integer index; 0 <= index < set -> size ==> set -> elements [ index ] == element );  
  @ ensures \result == \false ==> ( \forall integer index; 0 <= index < set -> size ==> set -> elements [ index ] != element );  
@*/
bool contains ( int element, DisjointSet * set ) {
    /*@
      @ loop invariant 0 <= i <= set -> size;
      @ loop assigns i;
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
  @ requires set != \null && \valid ( set );
  @ requires freeable_set ( * set );
  @ requires valid_parts ( * set );
  @ requires valid_sizes ( * set );
  @
  @ behavior no_set:
  @		assumes * set == \null && \allocable { Here } ( * set ); 
  @	
  @		allocates * set;		
  @		allocates ( * set ) -> elements;		
  @		allocates ( * set ) -> parents;
  @		allocates ( * set ) -> sizes;
  @
  @		assigns * set;		
  @		
  @		frees \nothing;		
  @		
  @		ensures ( * set ) -> elements [ 0 ] == element;
  @		ensures ( * set ) -> parents [ 0 ] == 0;
  @		ensures ( * set ) -> sizes [ 0 ] == 1;
  @     ensures freeable_set { Here } ( * set );
  @     ensures valid_parts ( * set );
  @     ensures valid_sizes ( * set );
  @		ensures \result == 0;
  @
  @ behavior resize_set:	
  @		assumes * set != \null && \freeable { Here } ( * set );
  @		assumes ( * set ) -> size >= ( * set ) -> capacity; 
  @ 	assumes \forall integer index; 0 <= index < ( * set ) -> size ==> ( * set ) -> elements [ index ] != element;
  @
  @		allocates * set;		
  @		allocates ( * set ) -> elements;		
  @		allocates ( * set ) -> parents;		
  @		allocates ( * set ) -> sizes;		
  @	
  @		assigns ( * set ) -> elements;	
  @		assigns ( * set ) -> elements [ 0 .. \old ( ( * set ) -> size ) ];	
  @		assigns ( * set ) -> parents;	
  @		assigns ( * set ) -> parents [ 0 .. \old ( ( * set ) -> size ) ];	
  @		assigns ( * set ) -> sizes;	
  @		assigns ( * set ) -> sizes [ 0 .. \old ( ( * set ) -> size ) ];	
  @		assigns ( * set ) -> capacity;	
  @		assigns ( * set ) -> size;	
  @	
  @		frees ( * set ) -> elements;		
  @		frees ( * set ) -> parents;		
  @	
  @		ensures ( * set ) -> elements [ \old ( ( * set ) -> size ) ] == element;
  @		ensures ( * set ) -> parents [ \old ( ( * set ) -> size ) ] == \old ( ( * set ) -> size );
  @		ensures ( * set ) -> sizes [ \old ( ( * set ) -> size ) ] == 1; 
  @     ensures freeable_set { Here } ( * set );
  @     ensures valid_parts ( * set );
  @     ensures valid_sizes ( * set );
  @		ensures \result == \old ( ( * set ) -> size );
  @	
  @ behavior no_resize_set:	
  @		assumes * set != \null && \freeable { Here } ( * set );
  @		assumes ( * set ) -> capacity < ( * set ) -> size; 		
  @ 	assumes \forall integer index; 0 <= index < ( * set ) -> size ==> ( * set ) -> elements [ index ] != element;
  @
  @		allocates \nothing;
  @
  @		assigns ( * set ) -> size;
  @		assigns ( * set ) -> elements [ \old ( ( * set ) -> size ) ];
  @		assigns ( * set ) -> parents [ \old ( ( * set ) -> size ) ];
  @		assigns ( * set ) -> sizes [ \old ( ( * set ) -> size ) ];
  @
  @		frees \nothing;
  @
  @		ensures ( * set ) -> elements [ \old ( ( * set ) -> size ) ] == element;
  @		ensures ( * set ) -> parents [ \old ( ( * set ) -> size ) ] == \old ( ( * set ) -> size );
  @		ensures ( * set ) -> sizes [ \old ( ( * set ) -> size ) ] == 1; 
  @     ensures freeable_set { Here } ( * set );
  @     ensures valid_parts ( * set );
  @     ensures valid_sizes ( * set );
  @		ensures \result == \old ( ( * set ) -> size );
  @
  @ behavior in_set:	
  @		assumes * set != \null && \freeable { Here } ( * set );
  @     assumes \exists integer index; 0 <= index < ( * set ) -> size ==> ( * set ) -> elements [ index ] == element; 
  @
  @		allocates \nothing;
  @
  @		assigns \nothing;
  @
  @		frees \nothing;
  @
  @     ensures freeable_set { Here } ( * set );
  @     ensures valid_parts ( * set );
  @     ensures valid_sizes ( * set );
  @		ensures \result == -1;
  @ 
  @ complete behaviors; 
*/
int makeSet ( int element, DisjointSet ** set  ) {
	if ( ( * set ) == NULL ) {
		* set = ( DisjointSet * ) malloc ( 1 * sizeof ( DisjointSet ) );
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
 
 
/*@
  @	requires freeable_set { Here } ( set );
  @ requires valid_parts ( set );
  @ requires valid_sizes ( set );
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
  @     ensures freeable_set { Here } ( set );
  @     ensures valid_parts ( set );
  @     ensures valid_sizes ( set );
  @     ensures \result == \true;
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
  @     ensures freeable_set { Here } ( set );
  @     ensures valid_parts ( set );
  @     ensures valid_sizes ( set );
  @     ensures \result == \false;
@*/
bool find ( int elementIndex, DisjointSet * set, int * setID ) {
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

/*@
  @ behavior swap:
  @     assumes first != \null && \valid ( first );
  @     assumes second != \null && \valid ( second );
  @
  @     assigns * first;
  @     assigns * second;
  @
  @     ensures first != \null && \valid ( first );
  @     ensures second != \null && \valid ( second );
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
  @ requires set != \null && \valid ( set );
  @	requires freeable_set { Here } ( * set );
  @ requires valid_parts ( * set );
  @ requires valid_sizes ( * set );
  @
  @ behavior valid:
  @     assumes 0 <= elementIndex1 < ( * set ) -> size;
  @     assumes 0 <= elementIndex2 < ( * set ) -> size;
  @
  @     allocates \nothing;
  @
  @     frees \nothing;
  @
  @		ensures freeable_set { Here } ( * set );
  @ 	ensures valid_parts ( * set );
  @ 	ensures valid_sizes ( * set );
  @     ensures \result == true;
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
  @		ensures freeable_set { Here } ( * set );
  @ 	ensures valid_parts ( * set );
  @ 	ensures valid_sizes ( * set );
  @     ensures \result == \false;
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

/*@
  @ requires freeable_set { Here } ( set );
  @ requires valid_parts ( set );
  @ requires valid_sizes ( set );
  @
  @ allocates \nothing;
  @
  @ assigns \nothing;
  @
  @ frees set;
  @ frees set -> elements;
  @ frees set -> parents;
  @ frees set -> sizes;
  @
  @ ensures \allocable { Here } ( set );
  @
@*/
void freeSet ( DisjointSet * set ) {
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
int main ( ) {
	DisjointSet * set = NULL;
    makeSet ( 1, & set );
    makeSet ( 2, & set );
    makeSet ( 3, & set );
    makeSet ( 4, & set );
    makeSet ( 5, & set );
    makeSet ( 6, & set );

    int value = 0;
    find ( 1, set, & value );
    find ( -333, set, & value );
    find ( 10, set, & value );

    unionSet ( 0, 1, & set );
    unionSet ( 2, 1, & set );
    unionSet ( 3, 4, & set );
    unionSet ( 4, 5, & set );
    unionSet ( 1, 5, & set );

    freeSet ( set );
	//@ assert 1 == 0;
    return 0;
}
