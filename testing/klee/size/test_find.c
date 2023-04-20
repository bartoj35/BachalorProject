#include "size.h"


int main ( void ) {
	UnionFind * set = NULL;

	for ( int i = 1; i <= 6; i ++ ) {
		makeSet ( i, & set );
	}

	int value = 0;
	unionSet ( 0, 1, set );
	unionSet ( 1, 2, set );

    int a;
    klee_make_symbolic ( & a, sizeof ( a ), "a" );
    find ( a, set );

	freeSet ( set );
	return 0;
}
