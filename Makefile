CXX				= gcc
CXXFLAGS		= -Wall -Werror -pedantic -O3 -o project


all: compile


compile:
	$(CXX) $(CXXFLAGS) main.c


clean:
	rm -rf project


run:
	./project
