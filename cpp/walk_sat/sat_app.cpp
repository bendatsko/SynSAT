#include <iostream>
#include <chrono>
#include "SAT.h"
#include <dirent.h>

// Helper function to count satisfied clauses
int countSatisfiedClauses(SAT* solver, const std::map<int, bool>& assignment) {
    int satisfied = 0;
    auto clauses = solver->get_clauses();
    for (const auto& clause : clauses) {
        if (solver->check_clause(clause, assignment)) {
            satisfied++;
        }
    }
    return satisfied;
}

std::map<int, bool> runWalkSAT(SAT* sat_solver, float p, int max_flips) {
    auto start = std::chrono::high_resolution_clock::now();
    std::map<int, bool> result = sat_solver->walk_sat(p, max_flips);
    auto stop = std::chrono::high_resolution_clock::now();

    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    std::cout << "Walk-SAT took " << duration.count() << " microseconds to run." << std::endl;

    // Add satisfaction check after each WalkSAT run
    std::cout << "Solution satisfies " << countSatisfiedClauses(sat_solver, result)
              << "/" << sat_solver->get_num_clauses() << " clauses" << std::endl;

    return result;
}

std::map<int, bool> splitAndSolve(char* file_path, double& first_half_avg, double& second_half_avg, double& refinement_avg) {
    SAT* sat_solver = new SAT();
    sat_solver->load_from_file(file_path);

    int num_variables = sat_solver->get_num_variables();
    int num_clauses = sat_solver->get_num_clauses();

    std::cout << "\nProblem stats:" << std::endl;
    std::cout << "Total variables: " << num_variables << std::endl;
    std::cout << "Total clauses: " << num_clauses << std::endl;

    // Split clauses
    auto all_clauses = sat_solver->get_clauses();
    int mid_point = all_clauses.size() / 2;

    std::vector<std::vector<int>> first_half;
    std::vector<std::vector<int>> second_half;

    for (size_t i = 0; i < all_clauses.size(); i++) {
        if (i < mid_point) {
            first_half.push_back(all_clauses[i]);
        } else {
            second_half.push_back(all_clauses[i]);
        }
    }

    // Create solvers
    SAT* first_half_solver = new SAT();
    first_half_solver->_clauses = first_half;
    first_half_solver->_num_clauses = first_half.size();
    first_half_solver->_num_variables = num_variables;

    SAT* second_half_solver = new SAT();
    second_half_solver->_clauses = second_half;
    second_half_solver->_num_clauses = second_half.size();
    second_half_solver->_num_variables = num_variables;

    std::cout << "\nSplit stats:" << std::endl;
    std::cout << "First half: " << first_half_solver->_num_clauses << " clauses" << std::endl;
    std::cout << "Second half: " << second_half_solver->_num_clauses << " clauses" << std::endl;

    // First half
    std::cout << "\nProcessing first half..." << std::endl;
    auto start = std::chrono::high_resolution_clock::now();
    std::map<int, bool> first_half_result = runWalkSAT(first_half_solver, 0.5, 5000);
    auto stop = std::chrono::high_resolution_clock::now();
    auto first_half_duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();
    first_half_avg += first_half_duration;

    // Second half
    std::cout << "\nProcessing second half..." << std::endl;
    second_half_solver->set_initial_assignment(first_half_result);
    start = std::chrono::high_resolution_clock::now();
    std::map<int, bool> second_half_result = runWalkSAT(second_half_solver, 0.5, 5000);
    stop = std::chrono::high_resolution_clock::now();
    auto second_half_duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();
    second_half_avg += second_half_duration;

    // Combine results
    std::map<int, bool> final_result = second_half_result;
    for (const auto& pair : first_half_result) {
        if (final_result.find(pair.first) == final_result.end()) {
            final_result[pair.first] = pair.second;
        }
    }

    std::cout << "\nCombined solution check:" << std::endl;
    std::cout << "Combined solution satisfies " << countSatisfiedClauses(sat_solver, final_result)
              << "/" << sat_solver->get_num_clauses() << " clauses" << std::endl;

    // Refinement Stage
    std::cout << "\nPre-refinement details:" << std::endl;
    int current_satisfied = countSatisfiedClauses(sat_solver, final_result);
    std::cout << "Satisfied clauses: " << current_satisfied << "/" << num_clauses << std::endl;

    std::cout << "\nRunning refinement..." << std::endl;
    start = std::chrono::high_resolution_clock::now();
    for (int i = 0; i < 500; ++i) {  // Limit to 500 refinement flips
        auto unsat_clauses = sat_solver->check_assignment(final_result);

        if (unsat_clauses.empty()) {
            break;  // All clauses satisfied
        }

        // Randomly select a clause from unsatisfied clauses
        auto clause = unsat_clauses[rand() % unsat_clauses.size()];

        // Identify the variable that maximizes satisfied clauses
        int best_var = 0;
        int max_satisfied = current_satisfied;
        for (int lit : clause) {
            int var = abs(lit);
            final_result[var] = !final_result[var];  // Flip the variable
            int new_satisfied = countSatisfiedClauses(sat_solver, final_result);
            if (new_satisfied > max_satisfied) {
                best_var = var;
                max_satisfied = new_satisfied;
            }
            final_result[var] = !final_result[var];  // Revert the flip
        }

        // Flip the best variable
        if (best_var != 0) {
            final_result[best_var] = !final_result[best_var];
            current_satisfied = max_satisfied;
        }
    }
    stop = std::chrono::high_resolution_clock::now();
    auto refinement_duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();
    refinement_avg += refinement_duration;

    std::cout << "Refinement satisfied clauses: " << current_satisfied << "/" << sat_solver->get_num_clauses() << std::endl;

    std::cout << "\nTiming breakdown:" << std::endl;
    std::cout << "First half: " << first_half_duration << " microseconds" << std::endl;
    std::cout << "Second half: " << second_half_duration << " microseconds" << std::endl;
    std::cout << "Refinement: " << refinement_duration << " microseconds" << std::endl;
    std::cout << "Total: " << (first_half_duration + second_half_duration + refinement_duration)
              << " microseconds" << std::endl;

    delete first_half_solver;
    delete second_half_solver;
    delete sat_solver;

    return final_result;
}

int main() {
    const int RUNS = 100;
    const int MAX_PROBLEMS = 2;
    std::string base_path = "../../sat_problems/uf50-218/uf50-0";
    double mono_total = 0;
    int num_tests = 0;
    double first_half_avg = 0, second_half_avg = 0, refinement_avg = 0;

    for(int i = 1; i <= MAX_PROBLEMS; i++) {
        std::string test_file = base_path + std::to_string(i) + ".cnf";
        SAT* sat_solver = new SAT();
        sat_solver->load_from_file(const_cast<char*>(test_file.c_str()));
        std::cout << "\nProblem " << i << "/" << MAX_PROBLEMS << ": " << test_file << std::endl;

        double mono_avg = 0;
        for(int r = 0; r < RUNS; r++) {
            std::cout << "\nRun " << r+1 << "/" << RUNS << std::endl;

            // Monolithic solve
            std::cout << "\nMonolithic solve:" << std::endl;
            auto start = std::chrono::high_resolution_clock::now();
            auto mono_result = sat_solver->walk_sat(0.5, 2000);
            auto stop = std::chrono::high_resolution_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start).count();
            mono_avg += duration;

            std::cout << "Monolithic solution satisfies " << countSatisfiedClauses(sat_solver, mono_result)
                      << "/" << sat_solver->get_num_clauses() << " clauses" << std::endl;

            // Split solve
            std::cout << "\nSplit solve:" << std::endl;
            splitAndSolve(const_cast<char*>(test_file.c_str()),
                         first_half_avg, second_half_avg, refinement_avg);
        }

        mono_avg /= RUNS;
        mono_total += mono_avg;
        num_tests++;

        std::cout << "\nProblem " << i << " Summary:" << std::endl;
        std::cout << "Monolithic avg: " << mono_avg << " microseconds" << std::endl;

        delete sat_solver;
    }

    std::cout << "\nFinal Results:" << std::endl;
    std::cout << "Tests run: " << num_tests << std::endl;
    std::cout << "Runs per test: " << RUNS << std::endl;
    std::cout << "Overall monolithic avg: " << mono_total/num_tests << " microseconds" << std::endl;
    std::cout << "Split components:" << std::endl;
    std::cout << "  First half avg: " << first_half_avg/(RUNS*num_tests) << " microseconds" << std::endl;
    std::cout << "  Second half avg: " << second_half_avg/(RUNS*num_tests) << " microseconds" << std::endl;
    std::cout << "  Refinement avg: " << refinement_avg/(RUNS*num_tests) << " microseconds" << std::endl;

    return 0;
}