#include "compression.h"


int main ( void ) {
	UnionFind * set = NULL;

	for ( int i = 1; i <= 6; i ++ ) {
		makeSet ( i, & set );
	}

	int a, b, c, d;
	klee_make_symbolic ( & a, sizeof ( a ), "a" );
	klee_make_symbolic ( & b, sizeof ( b ), "b" );
	klee_make_symbolic ( & b, sizeof ( b ), "c" );
	klee_make_symbolic ( & b, sizeof ( b ), "d" );
	
	unionSet ( a, b, set );
	unionSet ( c, d, set );
	
	freeSet ( set );
	return 0;
}

