#include "sat_search.h"
#include "search_common.h"

#include "../plugins/plugin.h"

using namespace std;

namespace plugin_sat {
class SATSearchFeature
    : public plugins::TypedFeature<SearchAlgorithm, sat_search::SATSearch> {
public:
    SATSearchFeature() : TypedFeature("sat") {
        document_title("SAT Search");
        document_synopsis("");

		add_option<bool>(
			"continue_after_first_plan",
			"Normally the planner stops once the first plan is found. If set to true, continue search even if a plan as been found.",
			"false");
	
		add_option<shared_ptr<sat_search::LengthStrategy>> (
			"length_strategy","strategy to determine plan lengths", "one_by_one()");
		add_option<shared_ptr<sat_search::SATEncodingFactory>> (
			"encoder","type of formula to use for encoding", "label_sat()");
	
		add_option<int>(
			"step_time_limit",
			"time limit for each step of the SAT run. Defaults to -1, which means no limit",
			"-1");
	
		add_option<bool>(
			"solver_quiet",
			"if possible try to put the SAT solver into quiet mode (less output to parse for experiments)",
			"false");
    	
		add_search_algorithm_options_to_feature(*this, "sat");
	}

    virtual shared_ptr<sat_search::SATSearch>
    create_component(const plugins::Options &opts) const override {
        return plugins::make_shared_from_arg_tuples<sat_search::SATSearch>(
			opts.get<int>("step_time_limit"),
			opts.get<bool>("continue_after_first_plan"),
			opts.get<shared_ptr<sat_search::LengthStrategy>>("length_strategy"),
			opts.get<shared_ptr<sat_search::SATEncodingFactory>>("encoder"),
			opts.get<bool>("solver_quiet"),
            get_search_algorithm_arguments_from_options(opts)
            );
    }
};

static plugins::FeaturePlugin<SATSearchFeature> _plugin;
}

