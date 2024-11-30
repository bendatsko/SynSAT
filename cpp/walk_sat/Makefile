# Compiler and flags
CXX = g++
CXXFLAGS = -std=c++11 -Wall -Wextra

# Targets and dependencies
all: sat

sat: sat_app.o SAT.o
	$(CXX) $(CXXFLAGS) -o sat sat_app.o SAT.o

sat_app.o: sat_app.cpp SAT.h
	$(CXX) $(CXXFLAGS) -c sat_app.cpp

SAT.o: SAT.cpp SAT.h
	$(CXX) $(CXXFLAGS) -c SAT.cpp

clean:
	rm -f *.o sat
