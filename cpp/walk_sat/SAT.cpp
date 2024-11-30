#include <iostream>
#include <fstream>
#include <assert.h>
#include <stdlib.h>
#include <string>
#include <vector>
#include <ctime>
#include <cstdlib>
#include <random>
#include <map>
#include "SAT.h"

const std::string END_OF_LINE = "0";
const char DELIMITER = ' ';

SAT::SAT() {
}

SAT::~SAT() {
}

std::vector<std::vector<int>> SAT::get_clauses() { return this->_clauses; }
int SAT::get_num_clauses() { return this->_num_clauses; }
int SAT::get_num_variables() { return this->_num_variables; }


void SAT::load_from_file(char* file_path) {
  std::string line;
  std::ifstream input_file (file_path);
  if (input_file.is_open()) {
    // Skip comments until we find the problem line
    while (getline(input_file, line)) {
      if (line.empty()) continue;
      if (line[0] == 'p') break;
    }

    // Parse the problem line
    std::vector<std::string> tokens = split(line, DELIMITER);
    // Format is "p cnf num_variables num_clauses"
    // Make sure we have enough tokens and they're valid
    if (tokens.size() < 4 || tokens[0] != "p" || tokens[1] != "cnf") {
      std::cerr << "Invalid problem line format" << std::endl;
      return;
    }

    this->_num_variables = std::stoi(tokens[2]);
    this->_num_clauses = std::stoi(tokens[3]);

    std::vector<std::vector<int>> clauses;

    while (getline(input_file, line)) {
      if (line.empty()) continue;
      if (line[0] == '%') break;  // End of clauses
      if (line[0] == 'c') continue;  // Skip comment lines

      tokens = split(line, DELIMITER);
      std::vector<int> clause;

      // Process each token in the line
      for (const auto& token : tokens) {
        if (token.empty()) continue;  // Skip empty tokens
        if (token == "0") break;      // End of clause
        try {
          clause.push_back(std::stoi(token));
        } catch (const std::invalid_argument& e) {
          // Skip invalid numbers
          continue;
        }
      }

      if (!clause.empty()) {
        clauses.push_back(clause);
      }
    }

    this->_clauses = clauses;
    this->_num_clauses = clauses.size();  // Update with actual count

    input_file.close();
  }
}

void SAT::set_initial_assignment(const std::map<int, bool>& initial_assignment) {
  // Set the model directly to the provided initial assignment
  this->_initial_model = initial_assignment;
}


std::vector<std::string> SAT::split(const std::string& sentence, char delimiter) {
  std::vector<std::string> tokens;
  std::string token;
  bool lastWasDelimiter = true;  // Handle leading spaces

  for (char c : sentence) {
    if (c == delimiter) {
      if (!lastWasDelimiter) {  // Only push token if we found a non-delimiter before
        tokens.push_back(token);
        token.clear();
      }
      lastWasDelimiter = true;
    } else {
      token += c;
      lastWasDelimiter = false;
    }
  }

  // Don't forget last token
  if (!token.empty()) {
    tokens.push_back(token);
  }

  return tokens;
}

std::map<int, bool> SAT::walk_sat(float p, int max_flips) {
    std::map<int, bool> model;
    std::map<int, bool> best_model;
    int best_satisfied = 0;

    if (!_initial_model.empty()) {
        model = _initial_model;
        best_model = model;
        best_satisfied = get_num_clauses() - check_assignment(model).size();
    } else {
        // Random initialization code...
        srand(time(0));
        for (int i = 1; i < this->_num_variables+1; i++) {
            model[i] = (rand() % 2 == 0 ? true : false);
        }
        best_model = model;
        best_satisfied = get_num_clauses() - check_assignment(model).size();
    }

    std::vector<std::vector<int>> unsat_clauses = check_assignment(model);

    // Track variables that appear in unsatisfied clauses
    std::vector<int> vars_to_consider;
    for (const auto& clause : unsat_clauses) {
        for (int lit : clause) {
            // Add var if not already in list
            int var = abs(lit);
            if (std::find(vars_to_consider.begin(), vars_to_consider.end(), var)
                == vars_to_consider.end()) {
                vars_to_consider.push_back(var);
            }
        }
    }

  int last_print = 0;
  int print_interval = max_flips / 10;  // Print every 10% progress


    int num_flips = 0;
    while (num_flips < max_flips) {

      if (num_flips - last_print >= print_interval) {
        std::cout << "Flip " << num_flips << "/" << max_flips
                  << ", Current satisfied: " << (get_num_clauses() - unsat_clauses.size())
                  << "/" << get_num_clauses() << std::endl;
        last_print = num_flips;
      }


        if (unsat_clauses.empty()) return model;

        // Track best solution
        int current_satisfied = get_num_clauses() - unsat_clauses.size();
        if (current_satisfied > best_satisfied) {
            best_satisfied = current_satisfied;
            best_model = model;

            // Update vars_to_consider based on new unsatisfied clauses
            vars_to_consider.clear();
            for (const auto& clause : unsat_clauses) {
                for (int lit : clause) {
                    int var = abs(lit);
                    if (std::find(vars_to_consider.begin(), vars_to_consider.end(), var)
                        == vars_to_consider.end()) {
                        vars_to_consider.push_back(var);
                    }
                }
            }
        }

        // Only choose from clauses we need to fix
        std::vector<int> choosen_clause = unsat_clauses[rand()%unsat_clauses.size()];
        int choosen_var;

        if ((rand() % 100) < (p * 100)) {  // p% chance of random move
            // Random selection but only from variables in unsatisfied clauses
            std::vector<int> possible_vars;
            for (int lit : choosen_clause) {
                possible_vars.push_back(abs(lit));
            }
            choosen_var = possible_vars[rand()%possible_vars.size()];
        } else {
            // Greedy selection but only consider flips that might fix unsatisfied clauses
            int max_sat = -1;
            for (int lit : choosen_clause) {
                int var = abs(lit);
                int sat_count = count_num_sat(var, model);
                if (sat_count > max_sat) {
                    choosen_var = var;
                    max_sat = sat_count;
                }
            }
        }

        model[choosen_var] = !model[choosen_var];
        unsat_clauses = check_assignment(model);
        num_flips++;
    }

    return best_model;
}

std::vector<std::vector<int>> SAT::check_assignment(const std::map<int, bool>& model) {
  std::vector<std::vector<int>> unsat_clauses;
  for (int i = 0; i < get_num_clauses(); i++){
    if (!check_clause(this->_clauses[i], model)){
      unsat_clauses.push_back(this->_clauses[i]);
    }
  }
  return unsat_clauses;
}

bool SAT::check_clause(const std::vector<int>& clause, const std::map<int, bool>& model) {
  for(std::vector<int>::const_iterator it = clause.begin(); it != clause.end(); ++it) {
    auto it_model = model.find(abs(*it));
    if (it_model != model.end()) {
      if (((*it > 0) && (it_model->second)) || ((*it < 0) && (!it_model->second))) {
        return true;
      }
    }
  }
  return false;
}

int SAT::count_num_sat(int var, std::map<int, bool>& model) {
  model[var] = !model[var];
  int sat_count = check_assignment(model).size();
  model[var] = !model[var];
  return sat_count;
}

void SAT::display_clauses() {
  for(std::vector<std::vector<int>>::iterator clause = _clauses.begin(); clause != _clauses.end(); ++clause){
    for (std::vector<int>::iterator literal = clause->begin(); literal != clause->end(); ++literal){
      std::cout << *literal << " ";
    }
    std::cout << std::endl;
  }
}

void SAT::display_model(const std::map<int, bool>& model) {
  for(std::map<int, bool>::const_iterator var = model.begin(); var != model.end(); ++var){
    std::cout << var->first << " " << var->second << std::endl;
  }
}
