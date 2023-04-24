import random

file = open(str(input(f'Enter name for the test file: ')), 'w')
set_size = int(input('Enter disjoint set size: '))
call_count = int(input('How many times should be operation called on set? '))


def beggining():
	file.write('\tDisjointSet * set = NULL;\n')
	file.write(f'\tfor ( int i = 0; i < {set_size}' + '; i ++ ) {\n')
	file.write('\t\tmakeSet ( i, & set );\n')
	file.write('\t}\n\n')


def union():
	a, b = random.randint(0, set_size - 1), random.randint(0, set_size - 1)
	file.write(f'\tunionSet ( {a}, {b}, set );\n')


def find():
	a = random.randint(0, set_size - 1)
	file.write(f'\tfind ( {a}, set );\n')


def value_var():
	file.write(f'\tint value = 0;\n')


def ending():
	file.write(f'\n\tprint ( set );\n')
	file.write(f'\tfreeSet ( set );\n')
	file.close()


beggining()
value_var()

for i in range(0,call_count):
	decide: int = random.randint(0,3)
	if decide == 0:
		find()
	else:
		union()

ending()

