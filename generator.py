import random

NEWLINE = '\n'
TAB = '\t'
LEFT_CURLY = '{'
RIGHT_CURLY = '}'
FILE_COUNT = 2


files = [open(str(input(f'Enter name for file{i}: ')) + '.c', 'w') for i in range(FILE_COUNT)]
n = int(input('Enter disjoint set size: '))

UNION_COUNT = 3 * n
FIND_COUNT = 2 * n

def beggining(file):
	file.write(f'void test ( ) {NEWLINE}')
	file.write(f'{TAB}DisjointSet * set = NULL;{NEWLINE}')
	file.write(f'{TAB}for ( int i = 0; i < {n}; i ++ ) {LEFT_CURLY}{NEWLINE}')
	file.write(f'{TAB}{TAB}makeSet ( i, & set );{NEWLINE}')
	file.write(f'{TAB}{RIGHT_CURLY}{NEWLINE}')
	file.write(f'{NEWLINE}')

def unions(files):
	for i in range(UNION_COUNT):
		a, b = random.randint(0, n - 1), random.randint(0, n - 1)
		for j in range(FILE_COUNT):
			files[j].write(f'{TAB}unionSet ( {a}, {b}, & set );{NEWLINE}')

def value_var(file):
	file.write(f'{NEWLINE}')
	file.write(f'{TAB}int value = 0;{NEWLINE}')

def ending(file):
	file.write(f'{NEWLINE}')
	file.write(f'{TAB}freeSet ( set );{NEWLINE}')
	file.write(f'{NEWLINE}')
	file.write(f'{TAB}return 0;{NEWLINE}')
	file.write('}\n')
	file.close()


for i in range(FILE_COUNT):
	beggining(files[i])

unions(files)

for i in range(FILE_COUNT):
	value_var(files[i])

for i in range(FIND_COUNT):
	a = random.randint(0, n - 1)
	files[0].write(f'{TAB}find ( {a}, set, & value );{NEWLINE}')
	files[1].write(f'{TAB}find ( {a}, & set, & value );{NEWLINE}')

for i in range(FILE_COUNT):
	ending(files[i])

