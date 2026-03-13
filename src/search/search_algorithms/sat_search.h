#ifndef SEARCH_ALGORITHMS_SAT_SEARCH
#define SEARCH_ALGORITHMS_SAT_SEARCH

#include "../search_algorithm.h"
#include "../sat/sat_encoder.h"
#include "../sat/sat_encoding.h"
//#include "../task_representation/transition_system.h"
//#include "../task_representation/label_equivalence_relation.h"


namespace plugins {
class Feature;
}


namespace sat_search{

class LengthStrategy;

class SATSearch : public SearchAlgorithm {
	const int stepTimeLimit;
	bool continueAfterFirstPlan;
	const std::shared_ptr<LengthStrategy> length_strategy;
	const std::shared_ptr<SATEncodingFactory> encoding_factory;

	// for iteration
	int stepNumber;
	int currentLength;

protected:
    virtual void initialize() override;
	virtual SearchStatus step() override;

public:
    explicit SATSearch(int _stepTimeLimit, bool _continueAfterFirstPlan, std::shared_ptr<LengthStrategy> _length_strategy, std::shared_ptr<SATEncodingFactory> _encoding_factory, bool _kissat_quietMode,int bound, double max_time, const std::string &description,  utils::Verbosity verbosity);
    virtual ~SATSearch() = default;

    virtual void print_statistics() const override;
};

extern void add_options_to_feature(plugins::Feature &feature);
}

#endif
