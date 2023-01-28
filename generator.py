import random

NEWLINE = '\n'
TAB = '\t'
LEFT_CURLY = '{'
RIGHT_CURLY = '}'
FILE_COUNT = 2


file = open(str(input(f'Enter name for the test file: ') + '.test'), 'w')
n = int(input('Enter disjoint set size: '))

UNION_COUNT = 3 * n
FIND_COUNT = 2 * n

def beggining():
	file.write(f'void test ( ) {LEFT_CURLY}{NEWLINE}')
	file.write(f'{TAB}DisjointSet * set = NULL;{NEWLINE}')
	file.write(f'{TAB}for ( int i = 0; i < {n}; i ++ ) {LEFT_CURLY}{NEWLINE}')
	file.write(f'{TAB}{TAB}makeSet ( i, & set );{NEWLINE}')
	file.write(f'{TAB}{RIGHT_CURLY}{NEWLINE}')
	file.write(f'{NEWLINE}')

def unions():
	for i in range(UNION_COUNT):
		a, b = random.randint(0, n - 1), random.randint(0, n - 1)
		file.write(f'{TAB}unionSet ( {a}, {b}, & set );{NEWLINE}')

def finds():
	for i in range(FIND_COUNT):
		a = random.randint(0, n - 1)
		file.write(f'{TAB}find ( {a}, ARG, & value );{NEWLINE}')



def value_var():
	file.write(f'{NEWLINE}')
	file.write(f'{TAB}int value = 0;{NEWLINE}')

def ending():
	file.write(f'{NEWLINE}')
	file.write(f'{TAB}print ( set );{NEWLINE}')
	file.write(f'{TAB}freeSet ( set );{NEWLINE}')
	file.write('}\n')
	file.close()


beggining()
unions()
value_var()
finds()
ending()

