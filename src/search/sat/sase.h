#ifndef SASE_H
#define SASE_H

#include "sat_encoder.h"
#include "sat_encoding.h"

#include <memory>

namespace sat_search {

class SaseEncodingFactory : public SATEncodingFactory {
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
    SaseEncoding(
        std::shared_ptr<sat_capsule> capsule, const TaskProxy _task_proxy,
        bool forceAtLeastOneAction);

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
