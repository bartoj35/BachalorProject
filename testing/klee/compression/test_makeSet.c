#include "compression.h" 


int main ( void ) {
	UnionFind * set = NULL;

	for ( int i = 1; i <= 6; i ++ ) {
		makeSet ( i, & set );
	}

    int a;
    klee_make_symbolic ( & a, sizeof ( a ), "a" );
    makeSet ( a, & set );

	freeSet ( set );
	return 0;
}
