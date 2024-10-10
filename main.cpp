#include <iostream>
#include <vector>
#include <string>
#include <cstdlib>
#include <algorithm>
#include <sstream>
#include <random>
#include <set>
#include <unordered_map>
#include <chrono>

using namespace std;
using namespace std::chrono;

struct Clause {
    int var1, var2, var3;
};

// Function to generate a satisfiable 3SAT problem
vector<Clause> generateSatisfiable3SATProblem(int numVars, int numClauses, vector<bool>& satisfyingAssignment) {
    vector<Clause> clauses;
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> varDist(1, numVars);
    uniform_int_distribution<> boolDist(0, 1);

    // Generate a random satisfying assignment
    satisfyingAssignment.resize(numVars);
    for (int i = 0; i < numVars; ++i) {
        satisfyingAssignment[i] = boolDist(gen);
    }

    // Generate clauses that are satisfied by the assignment
    for (int i = 0; i < numClauses; ++i) {
        int var1 = varDist(gen);
        int var2 = varDist(gen);
        int var3 = varDist(gen);

        // Decide the signs to ensure the clause is satisfied
        int sign1 = satisfyingAssignment[var1 - 1] ? 1 : -1;
        int sign2 = satisfyingAssignment[var2 - 1] ? 1 : -1;
        int sign3 = satisfyingAssignment[var3 - 1] ? 1 : -1;

        // To ensure the clause is satisfied, negate one literal randomly
        uniform_int_distribution<> negateDist(1, 3);
        int toNegate = negateDist(gen);
        if (toNegate == 1) sign1 *= -1;
        else if (toNegate == 2) sign2 *= -1;
        else sign3 *= -1;

        clauses.push_back({sign1 * var1, sign2 * var2, sign3 * var3});
    }

    return clauses;
}

// Evaluate a clause for a given assignment of variables
bool evaluateClause(const Clause& clause, const vector<bool>& assignment) {
    bool literal1 = clause.var1 > 0 ? assignment[clause.var1 - 1] : !assignment[-clause.var1 - 1];
    bool literal2 = clause.var2 > 0 ? assignment[clause.var2 - 1] : !assignment[-clause.var2 - 1];
    bool literal3 = clause.var3 > 0 ? assignment[clause.var3 - 1] : !assignment[-clause.var3 - 1];
    return literal1 || literal2 || literal3;
}

// WalkSAT algorithm with allowed variables and initial assignment
vector<bool> walkSAT(const vector<Clause>& clauses, int numVars, int maxFlips, int maxRestarts, const set<int>& allowedVars, const vector<bool>& initialAssignment = {}) {
    vector<bool> assignment(numVars, false); // Start with all variables set to false (0)

    random_device rd;
    mt19937 gen(rd());
    uniform_real_distribution<> probDist(0.0, 1.0);

    double p = 0.5; // Probability of random walk

    for (int restart = 0; restart < maxRestarts; ++restart) {
        // On each restart, re-initialize assignment to zeros
        if (!initialAssignment.empty()) {
            assignment = initialAssignment;
        } else {
            // Set allowed variables to zero
            for (int var : allowedVars) {
                assignment[var - 1] = false;
            }
        }

        for (int flip = 0; flip < maxFlips; ++flip) {
            vector<int> unsatClauses;

            // Find all unsatisfied clauses
            for (size_t i = 0; i < clauses.size(); ++i) {
                if (!evaluateClause(clauses[i], assignment)) {
                    unsatClauses.push_back(i);
                }
            }

            if (unsatClauses.empty()) {
                // Found a satisfying assignment
                return assignment;
            }

            // Select a random unsatisfied clause
            int randClauseIndex = unsatClauses[uniform_int_distribution<>(0, unsatClauses.size() - 1)(gen)];
            const Clause& clause = clauses[randClauseIndex];

            // Get allowed variables in the clause
            vector<int> varsInClause = {abs(clause.var1), abs(clause.var2), abs(clause.var3)};
            vector<int> allowedVarsInClause;
            for (int var : varsInClause) {
                if (allowedVars.count(var)) {
                    allowedVarsInClause.push_back(var);
                }
            }

            if (allowedVarsInClause.empty()) {
                // Can't flip any variable in this clause
                continue;
            }

            if (probDist(gen) < p) {
                // With probability p, flip a random allowed variable in the clause
                int idx = uniform_int_distribution<>(0, allowedVarsInClause.size() - 1)(gen);
                int varToFlip = allowedVarsInClause[idx];
                assignment[varToFlip - 1] = !assignment[varToFlip - 1];
            } else {
                // Otherwise, flip the variable that maximizes the number of satisfied clauses
                int bestVar = -1;
                int maxSatClauses = -1;
                for (int var : allowedVarsInClause) {
                    assignment[var - 1] = !assignment[var - 1];
                    int satClauses = 0;
                    for (size_t i = 0; i < clauses.size(); ++i) {
                        if (evaluateClause(clauses[i], assignment)) {
                            satClauses++;
                        }
                    }
                    if (satClauses > maxSatClauses) {
                        maxSatClauses = satClauses;
                        bestVar = var;
                    }
                    assignment[var - 1] = !assignment[var - 1]; // Flip back
                }
                if (bestVar != -1) {
                    assignment[bestVar - 1] = !assignment[bestVar - 1];
                }
            }
        }
    }

    // Return assignment even if a satisfying assignment wasn't found
    return assignment;
}

// Function to verify the correctness of the solution
bool verifySolution(const vector<Clause>& clauses, const vector<bool>& assignment) {
    for (const Clause& clause : clauses) {
        if (!evaluateClause(clause, assignment)) {
            return false;
        }
    }
    return true;
}

int main() {
    int numVars = 200;
    int numClauses = 456;
    vector<bool> originalAssignment;

    // Generate satisfiable 3SAT problem
    vector<Clause> problem = generateSatisfiable3SATProblem(numVars, numClauses, originalAssignment);

    // Display total number of clauses in the problem
    cout << "Total number of clauses in the problem: " << problem.size() << endl;

    // Prepare to solve without splitting
    set<int> allVars;
    for (int i = 1; i <= numVars; ++i) allVars.insert(i);

    // Solve the problem without splitting
    auto startNoSplit = high_resolution_clock::now();
    vector<bool> noSplitAssignment = walkSAT(problem, numVars, 10000, 100, allVars);
    auto endNoSplit = high_resolution_clock::now();
    auto durationNoSplit = duration_cast<microseconds>(endNoSplit - startNoSplit);
    cout << "No Split Total Time: " << durationNoSplit.count() << " microseconds\n";

    // Verify no split solution
    bool isNoSplitCorrect = verifySolution(problem, noSplitAssignment);
    cout << "No Split solution is " << (isNoSplitCorrect ? "correct!" : "incorrect!") << "\n";

    // Now perform split and solve
    // Split variables into two disjoint sets
    int midVar = numVars / 2;
    set<int> varsFirstHalf;
    set<int> varsSecondHalf;
    for (int i = 1; i <= midVar; ++i) varsFirstHalf.insert(i);
    for (int i = midVar + 1; i <= numVars; ++i) varsSecondHalf.insert(i);

    // Split clauses into three categories
    vector<Clause> firstHalfClauses;
    vector<Clause> secondHalfClauses;
    vector<Clause> crossClauses;

    for (const Clause& clause : problem) {
        bool inFirst = varsFirstHalf.count(abs(clause.var1)) && varsFirstHalf.count(abs(clause.var2)) && varsFirstHalf.count(abs(clause.var3));
        bool inSecond = varsSecondHalf.count(abs(clause.var1)) && varsSecondHalf.count(abs(clause.var2)) && varsSecondHalf.count(abs(clause.var3));

        if (inFirst) {
            firstHalfClauses.push_back(clause);
        } else if (inSecond) {
            secondHalfClauses.push_back(clause);
        } else {
            crossClauses.push_back(clause);
        }
    }

    cout << "First half has " << firstHalfClauses.size() << " clauses.\n";
    cout << "Second half has " << secondHalfClauses.size() << " clauses.\n";
    cout << "Cross clauses: " << crossClauses.size() << " clauses.\n";

    // Verify that the total number of clauses matches
    int totalClausesAfterSplit = firstHalfClauses.size() + secondHalfClauses.size() + crossClauses.size();
    cout << "Total clauses after splitting: " << totalClausesAfterSplit << endl;
    cout << "Verification that total clauses match: " << (totalClausesAfterSplit == problem.size() ? "Yes" : "No") << endl;

    // Solve first half
    auto startH1 = high_resolution_clock::now();
    vector<bool> assignmentFirstHalf = walkSAT(firstHalfClauses, numVars, 10000, 100, varsFirstHalf);
    auto endH1 = high_resolution_clock::now();
    auto durationH1 = duration_cast<microseconds>(endH1 - startH1);
    cout << "H1 Time: " << durationH1.count() << " microseconds\n";

    // Solve second half
    auto startH2 = high_resolution_clock::now();
    vector<bool> assignmentSecondHalf = walkSAT(secondHalfClauses, numVars, 10000, 100, varsSecondHalf);
    auto endH2 = high_resolution_clock::now();
    auto durationH2 = duration_cast<microseconds>(endH2 - startH2);
    cout << "H2 Time: " << durationH2.count() << " microseconds\n";

    // Combine assignments
    vector<bool> combinedAssignment = assignmentFirstHalf;
    for (int var : varsSecondHalf) {
        combinedAssignment[var - 1] = assignmentSecondHalf[var - 1];
    }

    // Refine solution on all clauses
    auto startRefine = high_resolution_clock::now();
    vector<bool> refinedAssignment = walkSAT(problem, numVars, 10000, 100, allVars, combinedAssignment);
    auto endRefine = high_resolution_clock::now();
    auto durationRefine = duration_cast<microseconds>(endRefine - startRefine);
    cout << "Step 2 Time (Global Refinement): " << durationRefine.count() << " microseconds\n";

    // Verify final solution
    bool isFinalCorrect = verifySolution(problem, refinedAssignment);
    cout << "Final solution is " << (isFinalCorrect ? "correct!" : "incorrect!") << "\n";

    return 0;
}
