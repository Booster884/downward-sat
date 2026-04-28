#include "sase.h"

#include "ipasir.h"
#include "sat_encoding.h"

#include <cassert>
#include <memory>
#include <tuple>
#include <vector>

namespace sat_search {

std::unique_ptr<SATEncoding> SaseEncodingFactory::createEncodingInstance(
    std::shared_ptr<sat_capsule> capsule) {
    return std::make_unique<SaseEncoding>(
        capsule, *task_proxy, forceAtLeastOneAction, *log);
}

void SaseEncodingFactory::initialize(
    const TaskProxy _task_proxy, utils::LogProxy _log) {
    task_proxy = std::make_shared<TaskProxy>(_task_proxy);
    log = std::make_shared<utils::LogProxy>(_log);
}

SaseEncoding::SaseEncoding(
    std::shared_ptr<sat_capsule> capsule, const TaskProxy _task_proxy,
    bool forceAtLeastOneAction, utils::LogProxy _log)
    : SATEncoding(capsule, _task_proxy, forceAtLeastOneAction), log(_log) {
    auto ops = task_proxy.get_operators();
    int n_vars = task_proxy.get_variables().size();

    for (size_t op_i = 0; op_i < ops.size(); op_i++) {
        auto op = ops[op_i];
        std::map<int, std::pair<int, int>> trs;

        for (int var_i = 0; var_i < n_vars; var_i++) {
            int pre = -1;
            int post = -1;
            for (auto const &cond : op.get_preconditions()) {
                if (cond.get_variable().get_id() != var_i)
                    continue;
                assert(post == -1);
                pre = cond.get_value();
            }
            for (auto const &eff : op.get_effects()) {
                if (eff.get_fact().get_variable().get_id() != var_i)
                    continue;
                assert(post == -1);
                post = eff.get_fact().get_value();
            }
            if (pre == -1 && post == -1)
                continue;

            if (post == -1) {
                post = pre;
            }
            trs[var_i] = std::pair(pre, post);
        }
        op_trs.push_back(trs);
    }
}

int SaseEncoding::get_transition_var(int time, int var_i, int from, int to) {
    int domain_size = task_proxy.get_variables()[var_i].get_domain_size();
    int tr_i = from * domain_size + to;
    return transition_vars.at(time).at(var_i).at(tr_i);
}

void SaseEncoding::generate_transition_vars(int time) {
    auto vars = task_proxy.get_variables();
    transition_vars[time].resize(vars.size());
    for (size_t var_i = 0; var_i < vars.size(); var_i++) {
        auto var = vars[var_i];
        int domain_size = var.get_domain_size();

        transition_vars[time][var_i].reserve(domain_size * domain_size);
        for (int from = 0; from < domain_size; from++) {
            for (int to = 0; to < domain_size; to++) {
                transition_vars[time][var_i].push_back(sat->new_variable());
            }
        }
    }
}

void SaseEncoding::generate_operator_vars(int time) {
    auto ops = task_proxy.get_operators();
    operator_vars[time].reserve(ops.size());
    for (size_t op_i = 0; op_i < ops.size(); op_i++) {
        operator_vars[time].push_back(sat->new_variable());
    }
}

void SaseEncoding::encode_progression(int time) {
    auto vars = task_proxy.get_variables();
    for (size_t var_i = 0; var_i < vars.size(); var_i++) {
        int domain_size = vars[var_i].get_domain_size();
        for (int h = 0; h < domain_size; h++) {
            std::vector<int> implied;
            for (int f = 0; f < domain_size; f++) {
                for (int g = 0; g < domain_size; g++) {
                    implied.push_back(get_transition_var(time, var_i, f, g));
                }
                sat->impliesOr(
                    get_transition_var(time - 1, var_i, h, f), implied);
            }
        }
    }
}

void SaseEncoding::encode_regression(int time) {
    auto vars = task_proxy.get_variables();
    for (size_t var_i = 0; var_i < vars.size(); var_i++) {
        int domain_size = vars[var_i].get_domain_size();
        for (int f = 0; f < domain_size; f++) {
            std::vector<int> implied;
            for (int g = 0; g < domain_size; g++) {
                for (int h = 0; h < domain_size; h++) {
                    implied.push_back(
                        get_transition_var(time - 1, var_i, h, f));
                }
                sat->impliesOr(get_transition_var(time, var_i, f, g), implied);
            }
        }
    }
}

void SaseEncoding::encode_tr_mutex(int time) {
    auto vars = task_proxy.get_variables();
    for (size_t var_i = 0; var_i < vars.size(); var_i++) {
        int domain_size = vars[var_i].get_domain_size();
        int n_trs = domain_size * domain_size;
        for (int tr_a = 0; tr_a < n_trs; tr_a++) {
            for (int tr_b = tr_a + 1; tr_b < n_trs; tr_b++) {
                sat->impliesNot(
                    transition_vars[time][var_i][tr_a],
                    transition_vars[time][var_i][tr_b]);
            }
        }
    }
}

void SaseEncoding::encode_op_composition(int time) {
    auto ops = task_proxy.get_operators();
    for (size_t op_i = 0; op_i < ops.size(); op_i++) {
        auto trs = op_trs[op_i];
        std::vector<int> implied;
        for (auto const &[var_i, tr] : trs) {
            auto [from, to] = tr;
            if (from == -1) {
                std::vector<int> implied;
                int domain_size =
                    task_proxy.get_variables()[var_i].get_domain_size();
                for (int from = 0; from < domain_size; from++) {
                    implied.push_back(
                        get_transition_var(time, var_i, from, to));
                }
                sat->impliesOr(operator_vars[time][op_i], implied);
            } else {
                implied.push_back(get_transition_var(time, var_i, from, to));
            }

            sat->impliesAnd(operator_vars[time][op_i], implied);
        }
    }
}

void SaseEncoding::encode_op_exists(int time) {
    auto ops = task_proxy.get_operators();
    auto vars = task_proxy.get_variables();
    for (size_t var_i = 0; var_i < vars.size(); var_i++) {
        int domain_size = vars[var_i].get_domain_size();
        for (int f = 0; f < domain_size; f++) {
            for (int g = 0; g < domain_size; g++) {
                std::vector<int> implied;
                if (f == g)
                    continue;

                for (int op_i = 0; op_i < ops.size(); op_i++) {
                    if (!op_trs[op_i].count(var_i))
                        continue;
                    auto [f_, g_] = op_trs[op_i][var_i];
                    if ((f_ == f || f_ == -1) && g_ == g) {
                        implied.push_back(operator_vars[time][op_i]);
                    }
                }
                if (!implied.empty()) {
                    sat->impliesOr(
                        get_transition_var(time, var_i, f, g), implied);
                } else {
                    sat->assertNot(get_transition_var(time, var_i, f, g));
                }
            }
        }
    }
}

void SaseEncoding::encode_op_mutex(int time) {
    // TODO
}

void SaseEncoding::encode(int fromTime, int toTime) {
    generate_transition_vars(fromTime);
    generate_operator_vars(fromTime);

    if (fromTime > 1) {
        encode_progression(fromTime);
        encode_regression(fromTime);
    }

    encode_tr_mutex(fromTime);
    encode_op_composition(fromTime);
    encode_op_exists(fromTime);
    encode_op_mutex(fromTime);
}

void SaseEncoding::encodeInit(int fromTime, bool retractable) {
    State init = task_proxy.get_initial_state();
    init.unpack();
    for (size_t i = 0; i < init.size(); i++) {
        FactProxy fact = init[i];
        int f = fact.get_value();
        int var_i = fact.get_variable().get_id();
        int domain_size = fact.get_variable().get_domain_size();

        std::vector<int> vars;
        vars.reserve(domain_size);
        for (int g = 0; g < domain_size; g++) {
            vars.push_back(get_transition_var(fromTime, var_i, f, g));
        }
        sat->atLeastOne(vars);
    }
}

void SaseEncoding::encodeGoal(int toTime, bool retractable) {
    GoalsProxy goals = task_proxy.get_goals();
    for (size_t i = 0; i < goals.size(); i++) {
        FactProxy fact = goals[i];
        int g = fact.get_value();
        int var_i = fact.get_variable().get_id();
        int domain_size = fact.get_variable().get_domain_size();

        std::vector<int> vars;
        vars.reserve(domain_size);
        for (int f = 0; f < domain_size; f++) {
            vars.push_back(get_transition_var(toTime - 1, var_i, f, g));
        }
        sat->atLeastOne(vars);
    }
}

void SaseEncoding::encodeStateEquals(
    int fromTime, int toTime, bool retractable) {
}

std::tuple<State, std::vector<State>, Plan> SaseEncoding::extractSolution(
    int initTime, std::vector<std::pair<int, int>> time_step_order) {
#ifndef NDEBUG
    log << "Transitions used:" << std::endl;
    auto vars = task_proxy.get_variables();
    for (size_t time = 0; time < transition_vars.size(); time++) {
        for (size_t var_i = 0; var_i < vars.size(); var_i++) {
            int domain_size = vars[var_i].get_domain_size();
            for (int f = 0; f < domain_size; f++) {
                for (int g = 0; g < domain_size; g++) {
                    int lit = get_transition_var(time + 1, var_i, f, g);
                    if (ipasir_val(sat->solver, lit) > 1) {
                        log << time + 1 << ") " << var_i << ": " << f << " -> "
                            << g << std::endl;
                    }
                }
            }
        }
    }
#endif

    Plan plan;

    DEBUG(log << "Actions taken:" << std::endl);
    auto ops = task_proxy.get_operators();
    for (size_t time = 0; time < operator_vars.size(); time++) {
        for (size_t op_i = 0; op_i < ops.size(); op_i++) {
            int lit = operator_vars[time + 1][op_i];
            if (ipasir_val(sat->solver, lit) > 1) {
                DEBUG(
                    log << time + 1 << ") " << ops[op_i].get_name()
                        << std::endl);
                plan.push_back(OperatorID(op_i));
            }
        }
    }

    DEBUG(log << "Applying operations" << std::endl);
    State curr = task_proxy.get_initial_state();
    std::vector<State> visited_states;
    visited_states.push_back(curr);
    for (size_t i = 0; i < plan.size(); i++) {
        DEBUG(log << "  " << ops[plan[i]].get_name() << std::endl);
        curr = curr.get_unregistered_successor(ops[plan[i]]);
        visited_states.push_back(curr);
    }
    return std::make_tuple(visited_states.back(), visited_states, plan);
}

// functions for debugging
void SaseEncoding::assertLabelsAtTime(int fromTime, std::set<int> labels) {
}

}
