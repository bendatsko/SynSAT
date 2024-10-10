#include <iostream>
#include <vector>
#include <cstdlib>
#include <random>
#include <set>
#include <chrono>

using namespace std::chrono;
using namespace std;

struct Clause {
    int var1, var2, var3;
};

// generate satisfiable 3SAT problem
vector<Clause> generateSatisfiable3SATProblem(int numVars, int numClauses, vector<bool> &satisfyingAssignment) {
    random_device rd;
    mt19937 gen(rd());

    vector<Clause> clauses;

    uniform_int_distribution<> varDist(1, numVars);
    uniform_int_distribution<> boolDist(0, 1);

    // generate random satisfying assignment
    satisfyingAssignment.resize(numVars);
    for (int i = 0; i < numVars; ++i) {
        satisfyingAssignment[i] = boolDist(gen);
    }

    // generate clauses
    for (int i = 0; i < numClauses; ++i) {
        int var1 = varDist(gen);
        int var2 = varDist(gen);
        int var3 = varDist(gen);

        // decide the signs to ensure the clause is satisfied
        int sign1 = satisfyingAssignment[var1 - 1] ? 1 : -1;
        int sign2 = satisfyingAssignment[var2 - 1] ? 1 : -1;
        int sign3 = satisfyingAssignment[var3 - 1] ? 1 : -1;

        // to ensure clause is satisfied, negate one literal randomly
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
bool evaluateClause(const Clause &clause, const vector<bool> &assignment) {
    bool literal1 = clause.var1 > 0 ? assignment[clause.var1 - 1] : !assignment[-clause.var1 - 1];
    bool literal2 = clause.var2 > 0 ? assignment[clause.var2 - 1] : !assignment[-clause.var2 - 1];
    bool literal3 = clause.var3 > 0 ? assignment[clause.var3 - 1] : !assignment[-clause.var3 - 1];
    return literal1 || literal2 || literal3;
}

// WalkSAT algorithm with allowed variables and initial assignment
vector<bool> walkSAT(const vector<Clause> &clauses, int numVars, int maxFlips, int maxRestarts,
                     const set<int> &allowedVars, const vector<bool> &initialAssignment = {}) {
    vector<bool> assignment(numVars, false); // start with all variables set to false aka 0

    random_device rd;
    mt19937 gen(rd());
    uniform_real_distribution<> probDist(0.0, 1.0);

    double p = 0.5; // probability of random walk

    for (int restart = 0; restart < maxRestarts; ++restart) {
        // on each restart, re-initialize assignment to zeros
        if (!initialAssignment.empty()) {
            assignment = initialAssignment;
        } else {
            // set allowed variables to zero
            for (int var: allowedVars) {
                assignment[var - 1] = false;
            }
        }

        for (int flip = 0; flip < maxFlips; ++flip) {
            vector<int> unsatClauses;

            // find all unsatisfied clauses
            for (size_t i = 0; i < clauses.size(); ++i) {
                if (!evaluateClause(clauses[i], assignment)) {
                    unsatClauses.push_back(i);
                }
            }

            if (unsatClauses.empty()) {
                // found a satisfying assignment
                return assignment;
            }

            // Select a random unsatisfied clause
            int randClauseIndex = unsatClauses[uniform_int_distribution<>(0, unsatClauses.size() - 1)(gen)];
            const Clause &clause = clauses[randClauseIndex];

            // Get allowed variables in the clause
            vector<int> varsInClause = {abs(clause.var1), abs(clause.var2), abs(clause.var3)};
            vector<int> allowedVarsInClause;
            for (int var: varsInClause) {
                if (allowedVars.count(var)) {
                    allowedVarsInClause.push_back(var);
                }
            }

            if (allowedVarsInClause.empty()) {
                // dont flip any var in this clause
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
                for (int var: allowedVarsInClause) {
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
                    assignment[var - 1] = !assignment[var - 1]; // flip back
                }
                if (bestVar != -1) {
                    assignment[bestVar - 1] = !assignment[bestVar - 1];
                }
            }
        }
    }

    // Return assignment even if a satisfying assignment isnt found
    return assignment;
}

// verify correctness
bool verifySolution(const vector<Clause> &clauses, const vector<bool> &assignment) {
    for (const Clause &clause: clauses) {
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

    vector<Clause> problem = generateSatisfiable3SATProblem(numVars, numClauses, originalAssignment);

    cout << "Total number of clauses in the problem: " << problem.size() << endl;

    // solve without splitting
    set<int> allVars;
    for (int i = 1; i <= numVars; ++i) allVars.insert(i);

    auto startNoSplit = high_resolution_clock::now();
    vector<bool> noSplitAssignment = walkSAT(problem, numVars, 10000, 100, allVars);
    auto endNoSplit = high_resolution_clock::now();
    auto durationNoSplit = duration_cast<microseconds>(endNoSplit - startNoSplit);
    cout << "No Split Total Time: " << durationNoSplit.count() << " microseconds\n";

    // verify no split solution
    bool isNoSplitCorrect = verifySolution(problem, noSplitAssignment);
    cout << "No Split solution is " << (isNoSplitCorrect ? "correct!" : "incorrect!") << "\n";

    // ------------------------------------------------------------------------------------------------------------
    //                                              split and solve
    // ------------------------------------------------------------------------------------------------------------

    // split vars into two disjoint sets
    int midVar = numVars / 2;
    set<int> varsFirstHalf;
    set<int> varsSecondHalf;
    for (int i = 1; i <= midVar; ++i) varsFirstHalf.insert(i);
    for (int i = midVar + 1; i <= numVars; ++i) varsSecondHalf.insert(i);

    // split clauses into three categories
    vector<Clause> firstHalfClauses;
    vector<Clause> secondHalfClauses;
    vector<Clause> crossClauses;

    for (const Clause &clause: problem) {
        bool inFirst = varsFirstHalf.count(abs(clause.var1)) && varsFirstHalf.count(abs(clause.var2)) && varsFirstHalf.
                       count(abs(clause.var3));
        bool inSecond = varsSecondHalf.count(abs(clause.var1)) && varsSecondHalf.count(abs(clause.var2)) &&
                        varsSecondHalf.count(abs(clause.var3));

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

    // verify total number of clauses matches. this is jank but i think it might work for now
    int totalClausesAfterSplit = firstHalfClauses.size() + secondHalfClauses.size() + crossClauses.size();
    cout << "Total clauses after splitting: " << totalClausesAfterSplit << endl;
    cout << "Verification that total clauses match: " << (totalClausesAfterSplit == problem.size() ? "Yes" : "No") <<
            endl;

    // solve first half
    auto startH1 = high_resolution_clock::now();
    vector<bool> assignmentFirstHalf = walkSAT(firstHalfClauses, numVars, 10000, 100, varsFirstHalf);
    auto endH1 = high_resolution_clock::now();
    auto durationH1 = duration_cast<microseconds>(endH1 - startH1);
    cout << "H1 Time: " << durationH1.count() << " microseconds\n";

    // solve second half
    auto startH2 = high_resolution_clock::now();
    vector<bool> assignmentSecondHalf = walkSAT(secondHalfClauses, numVars, 10000, 100, varsSecondHalf);
    auto endH2 = high_resolution_clock::now();
    auto durationH2 = duration_cast<microseconds>(endH2 - startH2);
    cout << "H2 Time: " << durationH2.count() << " microseconds\n";

    // combine assignments
    vector<bool> combinedAssignment = assignmentFirstHalf;
    for (int var: varsSecondHalf) {
        combinedAssignment[var - 1] = assignmentSecondHalf[var - 1];
    }

    // refine solution on all clauses
    auto startRefine = high_resolution_clock::now();
    vector<bool> refinedAssignment = walkSAT(problem, numVars, 10000, 100, allVars, combinedAssignment);
    auto endRefine = high_resolution_clock::now();
    auto durationRefine = duration_cast<microseconds>(endRefine - startRefine);
    cout << "Step 2 Time (Global Refinement): " << durationRefine.count() << " microseconds\n";

    // verify final solution
    bool isFinalCorrect = verifySolution(problem, refinedAssignment);
    cout << "Final solution is " << (isFinalCorrect ? "correct!" : "incorrect!") << "\n";

    return 0;
}
