XX			= g++
CXXFLAGS		= -Wall -Werror -pedantic -O3
CXXMEMFLAGS		= -g -fsanitize=address


all: compile_basic compile_rank compile_size compile_compression compile_splitting compile_halving thesis


compile_basic:
		$(CXX) $(CXXFLAGS) basicImplementation.c -o basic


compile_rank:
		$(CXX) $(CXXFLAGS) byRank.c	-o rank


compile_size:
		$(CXX) $(CXXFLAGS) bySize.c -o size


compile_compression:
		$(CXX) $(CXXFLAGS) pathCompression.c -o compression


compile_splitting:
		$(CXX) $(CXXFLAGS) pathSplitting.c -o splitting


compile_halving:
		$(CXX) $(CXXFLAGS) pathHalving.c -o halving


clean:
		rm -rf basic 
			rm -rf rank 
				rm -rf size 
					rm -rf compression
						rm -rf splitting
							rm -rf halving


memory_compile: memory_compile_basic memory_compile_rank memory_compile_size memory_compile_compression


memory_compile_basic:
		$(CXX) $(CXXMEMFLAGS) basicImplemention.c -o basic


memory_compile_rank:
		$(CXX) $(CXXMEMFLAGS) byRank.c	-o rank


memory_compile_size:
		$(CXX) $(CXXMEMFLAGS) bySize.c -o size


memory_compile_compression:
		$(CXX) $(CXXMEMFLAGS) pathCompression.c -o compression


memory_compile_splitting:
		$(CXX) $(CXXMEMFLAGS) pathSplitting.c -o splitting


memory_compile_halving:
		$(CXX) $(CXXMEMFLAGS) pathHalving.c -o halving


run_basic: compile_basic
		./basic


run_rank: compile_rank
		./rank


run_size: compile_size
		./size


run_compression: compile_compression
		./compression


run_splitting: compile_splitting
		./splitting


run_halving: compile_halving
		./halving

thesis:
	pdflatex -output-directory Thesis Thesis/disjointset.tex


