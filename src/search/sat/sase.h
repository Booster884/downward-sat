#ifndef SASE_H
#define SASE_H

#include "sat_encoder.h"
#include "sat_encoding.h"

#include <memory>

namespace sat_search {

class SaseEncodingFactory : public SATEncodingFactory {
public:
    std::vector<std::map<int, std::pair<int, int>>> op_trs;
public:
    SaseEncodingFactory(bool forceAtLeastOneAction)
        : SATEncodingFactory(forceAtLeastOneAction) {};

    virtual std::unique_ptr<SATEncoding> createEncodingInstance(
        std::shared_ptr<sat_capsule> capsule) override;
    virtual void initialize(
        const TaskProxy _task_proxy, utils::LogProxy _log) override;
};

class SaseEncoding : public SATEncoding {
public:
    std::map<int, std::vector<std::vector<int>>> transition_vars;
    std::map<int, std::vector<int>> operator_vars;

    int get_transition_var(int time, int var_i, int from, int to);

    void generate_transition_vars(int time);
    void generate_operator_vars(int time);

    void encode_progression(int time);
    void encode_regression(int time);
    void encode_tr_mutex(int time);
    void encode_op_composition(int time);
    void encode_op_exists(int time);
    void encode_op_mutex(int time);

public:
    mutable utils::LogProxy log;
    SaseEncodingFactory *factory;

    SaseEncoding(
        SaseEncodingFactory *_factory, std::shared_ptr<sat_capsule> capsule,
        const TaskProxy _task_proxy, bool forceAtLeastOneAction,
        utils::LogProxy _log);

    void encode(int fromTime, int toTime) override;
    void encodeInit(int fromTime, bool retractable) override;
    void encodeGoal(int toTime, bool retractable) override;
    void encodeStateEquals(int fromTime, int toTime, bool retractable) override;
    std::tuple<State, std::vector<State>, Plan> extractSolution(
        int initTime,
        std::vector<std::pair<int, int>> time_step_order) override;

    // functions for debugging
    void assertLabelsAtTime(int fromTime, std::set<int> labels) override;
};

}

#endif
