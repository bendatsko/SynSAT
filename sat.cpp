#include <iostream>
#include <vector>
#include <cstdlib>
#include <random>
#include <set>
#include <chrono>
#include <fstream>
#include <sstream>
#include <string>
#include <thread>
#include <iomanip>
#include <cmath>
#include <numeric>
using namespace std::chrono;
using namespace std;

// Basic structure for a 3-SAT clause
struct Clause {
    int var1, var2, var3;
};

struct Statistics {
    double average;
    double min;
    double max;
    double stddev;
};

Statistics computeStatistics(const vector<long long>& times) {
    double sum = accumulate(times.begin(), times.end(), 0.0);
    double mean = sum / times.size();

    double sq_sum = inner_product(times.begin(), times.end(), times.begin(), 0.0);
    double stddev = sqrt(sq_sum / times.size() - mean * mean);

    // Explicitly cast min and max values to double
    return {
        mean,
        static_cast<double>(*min_element(times.begin(), times.end())),
        static_cast<double>(*max_element(times.begin(), times.end())),
        stddev
    };
}

void printStatistics(const string& name, const Statistics& stats) {
    cout << name << ":\n";
    cout << "  Average: " << stats.average << " μs\n";
    cout << "  Min: " << stats.min << " μs\n";
    cout << "  Max: " << stats.max << " μs\n";
    cout << "  Stddev: " << stats.stddev << " μs\n";
    cout << endl;
}


//Now, let's implement the DIMACS parser. This needs to handle comment lines, find the problem definition, and read the clauses:
vector<Clause> parseDIMACS(const string& filename, int& numVars, int& numClauses) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "Error: Could not open file " << filename << endl;
        exit(1);
    }

    string line;
    vector<Clause> clauses;
    bool foundHeader = false;

    // Find problem line
    while (getline(file, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            istringstream iss(line);
            string p, cnf;
            iss >> p >> cnf >> numVars >> numClauses;
            foundHeader = true;
            break;
        }
    }

    if (!foundHeader) {
        cerr << "Error: No valid DIMACS header found in " << filename << endl;
        exit(1);
    }

    // Read clauses
    vector<int> currentClause;
    while (getline(file, line)) {
        if (line.empty() || line[0] == 'c' || line[0] == '%') continue;

        istringstream iss(line);
        int lit;
        while (iss >> lit) {
            if (lit == 0) {
                if (currentClause.size() == 3) {
                    clauses.push_back({currentClause[0], currentClause[1], currentClause[2]});
                }
                currentClause.clear();
            } else {
                currentClause.push_back(lit);
            }
        }
    }

    return clauses;
}

//Next, let's implement our core evaluation functions. These need to be efficient as they'll be called frequently:
bool evaluateClause(const Clause& clause, const vector<bool>& assignment) {
    bool literal1 = clause.var1 > 0 ? assignment[abs(clause.var1) - 1] : !assignment[abs(clause.var1) - 1];
    bool literal2 = clause.var2 > 0 ? assignment[abs(clause.var2) - 1] : !assignment[abs(clause.var2) - 1];
    bool literal3 = clause.var3 > 0 ? assignment[abs(clause.var3) - 1] : !assignment[abs(clause.var3) - 1];
    return literal1 || literal2 || literal3;
}

bool verifySolution(const vector<Clause>& clauses, const vector<bool>& assignment) {
    for (const Clause& clause : clauses) {
        if (!evaluateClause(clause, assignment)) {
            return false;
        }
    }
    return true;
}

//Now, the core WalkSAT implementation. This is the heart of our solver:
vector<bool> walkSAT(const vector<Clause>& clauses, int numVars, const set<int>& allowedVars,
                     const vector<bool>& initialAssignment = {}, int maxFlips = 1000, int maxRestarts = 10) {
    vector<bool> assignment(numVars);

    // cout << "Initial Assignment: ";
    // for (bool b : assignment) cout << (b ? "1 " : "0 ");
    // cout << endl;



    random_device rd;
    mt19937 gen(rd());
    uniform_real_distribution<> probDist(0.0, 1.0);
    double p = 0.4; // Probability of greedy move vs random walk

    for (int restart = 0; restart < maxRestarts; ++restart) {
        // Initialize assignment
        if (!initialAssignment.empty()) {
            assignment = initialAssignment;
        } else {
            for (int i = 0; i < numVars; i++) {
                assignment[i] = probDist(gen) < 0.5;
            }
        }

        for (int flip = 0; flip < maxFlips; ++flip) {
            // Find unsatisfied clauses that we can affect
            vector<int> unsatClauses;
            for (size_t i = 0; i < clauses.size(); ++i) {
                const Clause& c = clauses[i];
                if (!evaluateClause(c, assignment) &&
                    (allowedVars.count(abs(c.var1)) ||
                     allowedVars.count(abs(c.var2)) ||
                     allowedVars.count(abs(c.var3)))) {
                    unsatClauses.push_back(i);
                }
            }

            if (unsatClauses.empty()) {
                return assignment;
            }

            // Pick random unsatisfied clause
            int randClauseIdx = unsatClauses[uniform_int_distribution<>(0, unsatClauses.size() - 1)(gen)];
            const Clause& clause = clauses[randClauseIdx];

            // Get variables we're allowed to flip
            vector<int> varsInClause = {abs(clause.var1), abs(clause.var2), abs(clause.var3)};
            vector<int> allowedVarsInClause;
            for (int var : varsInClause) {
                if (allowedVars.count(var)) {
                    allowedVarsInClause.push_back(var);
                }
            }

            if (allowedVarsInClause.empty()) continue;

            // Make move
            if (probDist(gen) < p) {
                // Greedy move
                int bestVar = -1;
                int maxSatClauses = -1;
                for (int var : allowedVarsInClause) {
                    assignment[var - 1] = !assignment[var - 1];
                    int satClauses = 0;
                    for (const Clause& c : clauses) {
                        if (evaluateClause(c, assignment)) satClauses++;
                    }
                    if (satClauses > maxSatClauses) {
                        maxSatClauses = satClauses;
                        bestVar = var;
                    }
                    assignment[var - 1] = !assignment[var - 1];
                }
                if (bestVar != -1) {
                    assignment[bestVar - 1] = !assignment[bestVar - 1];
                }
            } else {
                // Random walk
                int varToFlip = allowedVarsInClause[uniform_int_distribution<>(0, allowedVarsInClause.size() - 1)(gen)];
                assignment[varToFlip - 1] = !assignment[varToFlip - 1];
            }
        }
    }
    return assignment;
}

vector<int> findUnsatisfiedClauses(const vector<Clause>& clauses, const vector<bool>& assignment) {
    vector<int> unsatClauses;
    for (size_t i = 0; i < clauses.size(); i++) {
        if (!evaluateClause(clauses[i], assignment)) {
            unsatClauses.push_back(i);
        }
    }
    return unsatClauses;
}

// Now let's implement the runTest function that manages our parallel solving approach:
void runTest(const string& filename) {
    // Parse input
    int numVars, numClauses;
    vector<Clause> problem = parseDIMACS(filename, numVars, numClauses);

    cout << "Processing " << filename << endl;
    cout << "Variables: " << numVars << ", Clauses: " << numClauses << endl;

    // Parallel Split + Refine approach
    cout << "\nApproach 1: Parallel Split + Refine" << endl;
    cout << "------------------------" << endl;

    int midVar = numVars / 2;
    set<int> firstHalf, secondHalf;
    for (int i = 1; i <= midVar; ++i) firstHalf.insert(i);
    for (int i = midVar + 1; i <= numVars; ++i) secondHalf.insert(i);

    vector<bool> firstHalfSolution(numVars, false), secondHalfSolution(numVars, false);
    bool firstHalfSatisfiable = false, secondHalfSatisfiable = false;
    long long firstHalfTime = 0, secondHalfTime = 0;

    auto startParallel = high_resolution_clock::now();

    // Solve first half in a thread
    thread core1([&]() {
        auto start = high_resolution_clock::now();
        firstHalfSolution = walkSAT(problem, numVars, firstHalf);
        auto end = high_resolution_clock::now();
        firstHalfTime = duration_cast<microseconds>(end - start).count();

        // Check satisfiability for first half
        vector<Clause> firstHalfClauses;
        for (const Clause& clause : problem) {
            if (firstHalf.count(abs(clause.var1)) &&
                firstHalf.count(abs(clause.var2)) &&
                firstHalf.count(abs(clause.var3))) {
                firstHalfClauses.push_back(clause);
            }
        }
        firstHalfSatisfiable = verifySolution(firstHalfClauses, firstHalfSolution);
    });

    // Solve second half in a thread
    thread core2([&]() {
        auto start = high_resolution_clock::now();
        secondHalfSolution = walkSAT(problem, numVars, secondHalf);
        auto end = high_resolution_clock::now();
        secondHalfTime = duration_cast<microseconds>(end - start).count();

        // Check satisfiability for second half
        vector<Clause> secondHalfClauses;
        for (const Clause& clause : problem) {
            if (secondHalf.count(abs(clause.var1)) &&
                secondHalf.count(abs(clause.var2)) &&
                secondHalf.count(abs(clause.var3))) {
                secondHalfClauses.push_back(clause);
            }
        }
        secondHalfSatisfiable = verifySolution(secondHalfClauses, secondHalfSolution);
    });

    core1.join();
    core2.join();

    auto endParallel = high_resolution_clock::now();
    auto parallelTime = duration_cast<microseconds>(endParallel - startParallel).count();

    // Output partial solutions, their satisfiability, and time taken
    cout << "First Half Partial Solution: ";
    for (int i = 0; i < midVar; ++i) {
        cout << (firstHalfSolution[i] ? i + 1 : -(i + 1)) << " ";
    }
    cout << "\nSatisfiable: " << (firstHalfSatisfiable ? "Yes" : "No") << endl;
    cout << "Time to solve first half: " << firstHalfTime << " μs\n";

    cout << "Second Half Partial Solution: ";
    for (int i = midVar; i < numVars; ++i) {
        cout << (secondHalfSolution[i] ? i + 1 : -(i + 1)) << " ";
    }
    cout << "\nSatisfiable: " << (secondHalfSatisfiable ? "Yes" : "No") << endl;
    cout << "Time to solve second half: " << secondHalfTime << " μs\n";

    // Merge partial solutions
    vector<bool> combinedSolution = firstHalfSolution;
    for (int i = midVar; i < numVars; ++i) {
        combinedSolution[i] = secondHalfSolution[i];
    }

    // Verify combined solution
    bool splitSolved = verifySolution(problem, combinedSolution);

    cout << "Combined Solution: ";
    for (int i = 0; i < numVars; ++i) {
        cout << (combinedSolution[i] ? i + 1 : -(i + 1)) << " ";
    }
    cout << "\nCombined Satisfiability: " << (splitSolved ? "Yes" : "No") << endl;

    // Refine solution if not satisfiable
    if (!splitSolved) {
        cout << "\nRefining combined solution..." << endl;
        auto startRefine = high_resolution_clock::now();

        set<int> allVars;
        for (int i = 1; i <= numVars; ++i) allVars.insert(i);

        vector<bool> refinedSolution = walkSAT(problem, numVars, allVars, combinedSolution);

        auto endRefine = high_resolution_clock::now();
        auto refineTime = duration_cast<microseconds>(endRefine - startRefine).count();

        bool refinedSatisfiable = verifySolution(problem, refinedSolution);

        cout << "Refined Solution: ";
        for (int i = 0; i < numVars; ++i) {
            cout << (refinedSolution[i] ? i + 1 : -(i + 1)) << " ";
        }
        cout << "\nRefined Satisfiability: " << (refinedSatisfiable ? "Yes" : "No") << endl;
        cout << "Refinement time: " << refineTime << " μs\n";
    }

    cout << "Parallel time: " << parallelTime << " μs\n";

    // Single WalkSAT approach
    cout << "\nApproach 2: Single WalkSAT" << endl;
    cout << "------------------------" << endl;

    set<int> allVars;
    for (int i = 1; i <= numVars; ++i) allVars.insert(i);

    auto startSingle = high_resolution_clock::now();
    vector<bool> singleSolution = walkSAT(problem, numVars, allVars);
    bool singleSolved = verifySolution(problem, singleSolution);
    auto endSingle = high_resolution_clock::now();
    auto singleTime = duration_cast<microseconds>(endSingle - startSingle).count();

    cout << (singleSolved ? "s SATISFIABLE" : "s UNSATISFIABLE") << endl;
    cout << "v ";
    for (int i = 0; i < numVars; ++i) {
        cout << (singleSolution[i] ? i + 1 : -(i + 1)) << " ";
    }
    cout << "0" << endl;

    cout << "Single WalkSAT time: " << singleTime << " μs\n";
}



int main() {
    const int numRuns = 1000; // Number of iterations for statistics
    const string filename = "uf20-91/uf20-01.cnf";

    vector<long long> firstHalfTimes, secondHalfTimes, refineTimes, parallelTimes, singleTimes;
    int parallelSuccessCount = 0, singleSuccessCount = 0;

    for (int i = 0; i < numRuns; i++) {
        cout << "Run " << i + 1 << "/" << numRuns << endl;

        // Parse input
        int numVars, numClauses;
        vector<Clause> problem = parseDIMACS(filename, numVars, numClauses);

        // Run parallel split + refine
        int midVar = numVars / 2;
        set<int> firstHalf, secondHalf;
        for (int i = 1; i <= midVar; ++i) firstHalf.insert(i);
        for (int i = midVar + 1; i <= numVars; ++i) secondHalf.insert(i);

        vector<bool> firstHalfSolution(numVars, false), secondHalfSolution(numVars, false);
        long long firstHalfTime = 0, secondHalfTime = 0, refineTime = 0;
        bool splitSolved = false, refinedSolved = false;

        auto startParallel = high_resolution_clock::now();

        thread core1([&]() {
            auto start = high_resolution_clock::now();
            firstHalfSolution = walkSAT(problem, numVars, firstHalf);
            auto end = high_resolution_clock::now();
            firstHalfTime = duration_cast<microseconds>(end - start).count();
        });

        thread core2([&]() {
            auto start = high_resolution_clock::now();
            secondHalfSolution = walkSAT(problem, numVars, secondHalf);
            auto end = high_resolution_clock::now();
            secondHalfTime = duration_cast<microseconds>(end - start).count();
        });

        core1.join();
        core2.join();

        vector<bool> combinedSolution = firstHalfSolution;
        for (int i = midVar; i < numVars; ++i) {
            combinedSolution[i] = secondHalfSolution[i];
        }

        splitSolved = verifySolution(problem, combinedSolution);
        auto endParallel = high_resolution_clock::now();
        long long parallelTime = duration_cast<microseconds>(endParallel - startParallel).count();

        if (!splitSolved) {
            auto startRefine = high_resolution_clock::now();
            set<int> allVars;
            for (int i = 1; i <= numVars; ++i) allVars.insert(i);

            combinedSolution = walkSAT(problem, numVars, allVars, combinedSolution);
            auto endRefine = high_resolution_clock::now();
            refineTime = duration_cast<microseconds>(endRefine - startRefine).count();

            refinedSolved = verifySolution(problem, combinedSolution);
        }

        firstHalfTimes.push_back(firstHalfTime);
        secondHalfTimes.push_back(secondHalfTime);
        refineTimes.push_back(refineTime);
        parallelTimes.push_back(parallelTime);

        if (splitSolved || refinedSolved) {
            parallelSuccessCount++;
        }

        // Run single WalkSAT
        auto startSingle = high_resolution_clock::now();
        set<int> allVars;
        for (int i = 1; i <= numVars; ++i) allVars.insert(i);

        vector<bool> singleSolution = walkSAT(problem, numVars, allVars);
        auto endSingle = high_resolution_clock::now();
        long long singleTime = duration_cast<microseconds>(endSingle - startSingle).count();

        singleTimes.push_back(singleTime);

        if (verifySolution(problem, singleSolution)) {
            singleSuccessCount++;
        }
    }

    // Compute statistics
    Statistics firstHalfStats = computeStatistics(firstHalfTimes);
    Statistics secondHalfStats = computeStatistics(secondHalfTimes);
    Statistics refineStats = computeStatistics(refineTimes);
    Statistics parallelStats = computeStatistics(parallelTimes);
    Statistics singleStats = computeStatistics(singleTimes);

    // Print results
    cout << "\nSummary of Results:\n";
    cout << "----------------------------------------\n";
    printStatistics("First Half Solve Time", firstHalfStats);
    printStatistics("Second Half Solve Time", secondHalfStats);
    printStatistics("Refinement Time", refineStats);
    printStatistics("Parallel Approach Total Time", parallelStats);
    printStatistics("Single WalkSAT Time", singleStats);

    cout << "Parallel Success Count: " << parallelSuccessCount << "/" << numRuns << endl;
    cout << "Single WalkSAT Success Count: " << singleSuccessCount << "/" << numRuns << endl;

    return 0;
}