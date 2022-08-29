CXX				= gcc
CXXFLAGS		= -Wall -Werror -pedantic -O3 -o project
CXXMEMFLAGS		= -g -fsanitize=address


all: compile


compile:
	$(CXX) $(CXXFLAGS) main.c


clean:
	rm -rf project


memory_compile:
	$(CXX) $(CXXMEMFLAGS) main.c


run: compile
	./project
