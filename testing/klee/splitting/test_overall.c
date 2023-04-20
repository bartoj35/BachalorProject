#include "splitting.h"


int main ( void ) {
	UnionFind * set = NULL;

	for ( int i = 1; i <= 6; i ++ ) {
		makeSet ( i, & set );
	}

	int a;
	klee_make_symbolic ( & a, sizeof ( a ), "a" );
    makeSet ( a, & set );
	
	int b;
	klee_make_symbolic ( & b, sizeof ( b ), "b" );
	find ( b, set );

	int c, d;
	klee_make_symbolic ( & c, sizeof ( c ), "c" );
	klee_make_symbolic ( & d, sizeof ( d ), "d" );
	
	unionSet ( c, d, set );
	
	int e;
	klee_make_symbolic ( & e, sizeof ( e ), "e" );
	find ( e, set );

	freeSet ( set );
	return 0;
}

