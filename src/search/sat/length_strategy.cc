#include "length_strategy.h"

#include <cmath>

#include "../plugins/plugin.h"

using namespace std;


namespace sat_search {

	// Constant length strategy
	LengthStrategyConstant::LengthStrategyConstant(int _plan_length) :
		plan_length(_plan_length) {
    }

    LengthStrategyByIteration::LengthStrategyByIteration(int _start_length, double _multiplier, int _maximum_iteration) :
		start_length(_start_length),
        multiplier(_multiplier),
        maximum_iteration(_maximum_iteration) {
    }

    std::optional<int> LengthStrategyByIteration::get_next_length(int step_number, int) const {
        if (step_number == maximum_iteration) {
            return std::nullopt;
        }
        return lround(0.5 + start_length * std::pow(multiplier, step_number));
    }



	///////////////////////////////
	// Plugins
	static class LengthStrategyCategoryPlugin : public plugins::TypedCategoryPlugin<LengthStrategy> {
	public:
	    LengthStrategyCategoryPlugin() : TypedCategoryPlugin("LengthStrategy") {
	        document_synopsis(
	            "This page describes the various length strategies supported by the planner.");
	    }
	}
	_category_plugin;


	class OneByOneStrategyFeature
	    : public plugins::TypedFeature<LengthStrategy, LengthStrategyOneByOne> {
	public:
	    OneByOneStrategyFeature() : TypedFeature("one_by_one") {
	        document_title("One by one iteration");
	        document_synopsis(
	            "");
	    }
	    virtual shared_ptr<LengthStrategyOneByOne>
	    create_component(const plugins::Options &opts) const override {
	        return plugins::make_shared_from_arg_tuples<LengthStrategyOneByOne>(
	            //opts.get<shared_ptr<MergeTreeFactory>>("merge_tree"),
	            //get_merge_strategy_arguments_from_options(opts)
	            );
	    }
	};
	
	static plugins::FeaturePlugin<OneByOneStrategyFeature> _plugin_one_by_one;


	class ByIterationStrategyFeature
	    : public plugins::TypedFeature<LengthStrategy, LengthStrategyByIteration> {
	public:
	    ByIterationStrategyFeature() : TypedFeature("by_iteration") {
	        document_title("By iteration");
	        document_synopsis(
	            "");
	
        	add_option<int>(
        	    "start_length",
        	    "Start value for plan length. Further lengths will be start_length * (multiplier)^iteration.",
        	    "5");
        	add_option<int>(
	    	    "maximum_iteration",
    		    "Number of iterations to be performed. If set to -1, there is no limit. ",
       			"-1");

        	add_option<double>(
        	    "multiplier",
        	    "Multiplier for iteration.",
        	    "1.41");
	    }
	    virtual shared_ptr<LengthStrategyByIteration>
	    create_component(const plugins::Options &opts) const override {
	        return plugins::make_shared_from_arg_tuples<LengthStrategyByIteration>(
					opts.get<int>("start_length"),
				    opts.get<double>("multiplier"),
			        opts.get<int>("maximum_iteration")
	            );
	    }
	};
	
	static plugins::FeaturePlugin<ByIterationStrategyFeature> _plugin_by_iteration;

	class ConstantStrategyFeature
	    : public plugins::TypedFeature<LengthStrategy, LengthStrategyConstant> {
	public:
	    ConstantStrategyFeature() : TypedFeature("constant") {
	        document_title("Constant");
	        document_synopsis(
	            "");
	        
			add_option<int>(
    	        "plan_length",
        	    "the plan length to try");
	
	    }
	    virtual shared_ptr<LengthStrategyConstant>
	    create_component(const plugins::Options &opts) const override {
	        return plugins::make_shared_from_arg_tuples<LengthStrategyConstant>(
					opts.get<int>("plan_length")
	            );
	    }
	};
	
	static plugins::FeaturePlugin<ConstantStrategyFeature> _plugin_constant;
}
