#include "sase.h"

#include "sat_encoding.h"

#include <memory>
#include <tuple>
#include <vector>

namespace sat_search {

std::unique_ptr<SATEncoding> SaseEncodingFactory::createEncodingInstance(
    std::shared_ptr<sat_capsule> capsule) {
    return std::make_unique<SaseEncoding>(
        capsule, *task_proxy, forceAtLeastOneAction);
}

void SaseEncodingFactory::initialize(
    const TaskProxy _task_proxy, utils::LogProxy _log) {
}

SaseEncoding::SaseEncoding(
    std::shared_ptr<sat_capsule> capsule, const TaskProxy _task_proxy,
    bool forceAtLeastOneAction)
    : SATEncoding(capsule, _task_proxy, forceAtLeastOneAction) {
}

void SaseEncoding::encode(int fromTime, int toTime) {
}

void SaseEncoding::encodeInit(int fromTime, bool retractable) {
}

void SaseEncoding::encodeGoal(int toTime, bool retractable) {
}

void SaseEncoding::encodeStateEquals(
    int fromTime, int toTime, bool retractable) {
}

std::tuple<State, std::vector<State>, Plan> SaseEncoding::extractSolution(
    int initTime, std::vector<std::pair<int, int>> time_step_order) {
    Plan plan;
    State curr = task_proxy.get_initial_state();
    std::vector<State> visited_states;
    visited_states.push_back(curr);
    return std::make_tuple(visited_states.back(), visited_states, plan);
}

// functions for debugging
void SaseEncoding::assertLabelsAtTime(int fromTime, std::set<int> labels) {
}

}
