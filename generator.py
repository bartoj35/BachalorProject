import random

file = open(str(input(f'Enter name for the test file: ')), 'w')
set_size = int(input('Enter disjoint set size: '))


UNION_COUNT = 3 * set_size
FIND_COUNT = 2 * set_size


def beggining():
	file.write('\tDisjointSet * set = NULL;\n')
	file.write(f'\tfor ( int i = 0; i < {set_size}' + '; i ++ ) {\n')
	file.write('\t\tmakeSet ( i, & set );\n')
	file.write('\t}\n\n')


def unions():
	for i in range(UNION_COUNT):
		a, b = random.randint(0, set_size - 1), random.randint(0, set_size - 1)
		file.write(f'\tunionSet ( {a}, {b}, & set );\n')


def finds():
	for i in range(FIND_COUNT):
		a = random.randint(0, set_size - 1)
		file.write(f'\tfind ( {a}, ARG, & value );\n')


def value_var():
	file.write(f'\n\tint value = 0;\n')


def ending():
	file.write(f'\n\tprint ( set );\n')
	file.write(f'\tfreeSet ( set );\n')
	file.close()


beggining()
unions()
value_var()
finds()
ending()

