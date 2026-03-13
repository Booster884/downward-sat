#ifndef KAUTZ_SELMAN_RINTANEN_H
#define KAUTZ_SELMAN_RINTANEN_H

#include "sat_encoder.h"
#include "sat_encoding.h"
#include "../utils/logging.h"

#include <memory>
#include <vector>
#include <map>
#include <set>


namespace sat_search {

struct AxiomSCC{
	std::vector<int> variables;
	bool sizeOne = false;
	bool isOfImplicationType = false;
	bool isDependentOnOneVariableInternally = false;
	int dependingVariable = false;


	bool fullComputationRequired = false;
	int numberOfAxiomLayers;

	// preprocessing information implications
	std::vector<std::vector<int>> directTransitiveImplications;
	std::vector<std::vector<int>> directTransitiveCauses;

	// preprocessing information guarded implications (i.e. ones that depend on a variable value)
	std::vector<std::vector<std::vector<int>>> guardedTransitiveImplications;
	std::vector<std::vector<std::vector<int>>> guardedTransitiveCauses;
	
};

class KautzSelmanRintanenEncoding : public SATEncoding {
public:
	// debugging / output configuration
	bool logInference = false;
	
	// actual run configuration
	int planLength;
	int currentLength;
	int lengthIteration;
	int startLength;
	double multiplier;
	bool existsStep = true;
	int disablingThreshold;
	bool aboveThresholdGroupJoining;
	bool useRintanensP;
	bool disableVARElimination;

	bool forceAtLeastOneAction;


	// TODO fill and use this map
	std::map<int,std::map<int,int>> operator_precondition_map;	

	// static knowledge about the problem:
	// whether a derived predicate is statically true
	std::unordered_set<int> statically_true_derived_predicates;


	// dynamic variables generated while creating the formula
	// index: timestep -> operator 
	std::map<int,std::vector<int>> operator_variables;

	// index: timestep -> variable -> value
	std::map<int,std::vector<std::vector<int>>> fact_variables;
	int get_fact_var(int time, FactProxy fact);
	int get_fact_var(int time, FactPair fact);

	// index: timestep -> variable
	std::map<int,std::vector<std::vector<int>>> axiom_variables;
	int get_axiom_var(int time, int layer, FactProxy fact);
	int get_axiom_var(int time, int layer, FactPair fact);
	int get_last_axiom_var(int time, FactProxy fact);
	int get_last_axiom_var(int time, FactPair fact);

	// index: timestep -> variable -> value -> list of causes
	std::map<int,std::vector<std::vector<std::vector<int>>>> achieverVars;
	std::map<int,std::vector<std::vector<std::vector<int>>>> deleterVars;




	//// variable -> value -> list of actions
	//std::vector<std::vector<std::vector<int>>> achiever;
	//std::vector<std::vector<std::vector<int>>> deleter;

	// axiom structure graph
	std::vector<std::vector<int>> derived_implication;
	std::vector<std::vector<int>> pos_derived_implication;
	std::vector<std::vector<int>> neg_derived_implication;
	std::map<FactPair, std::vector<int>> derived_entry_edges;
	void axiom_dfs(int var, std::set<int> & posReachable, std::set<int> & negReachable, bool mode);



	// axiom SCCs
	std::vector<AxiomSCC> axiomSCCsInTopOrder;
	std::map<int,int> numberOfAxiomLayerVariablesPerDerived;
	std::vector<std::vector<OperatorProxy>> achievers_per_derived;

	void axiom_encoding_for_timestep(int time);
	
	void printVariableTruth();


	bool try_to_satisfy(std::set<int> & activeAxtioms, std::set<FactPair> & currentState, FactPair goal);


	void compute_necessary_effects(int op, FactPair assumedFact,
		std::set<FactPair> & maintainedFacts,
		std::set<FactPair> & potentialEffects,
		std::set<FactPair> & definitiveEffects,
			bool evaluateAxiomsAfter);

	std::set<FactPair> evaluate_axioms_on_partial_state(std::set<FactPair> & definitiveEffects);
	
	void speculative_evaluate_axioms_on_partial_state(
			std::set<FactPair> & maintainedFacts,
			std::set<FactPair> & possibleEffects, std::set<FactPair> & definitiveEffects);


	std::set<FactPair> compute_known_prior_state(int op, FactPair assumedFact);


	// efficient access data structure, needed for testing whether two action have compatible preconditions and effect
	// these are the tests can_be_executed_in_same_state and have_actions_unconflicting_effects
	// static information about the planning problem.
    std::vector<std::vector<FactPair>> sorted_op_preconditions;
    std::vector<std::vector<FactPair>> sorted_op_effects;
	void set_up_efficient_conflict_testing();
	bool can_be_executed_in_same_state(int op1_no, int op2_no);
	bool have_actions_unconflicting_effects(int op1_no, int op2_no);


	// exists step
	std::vector<int> global_action_ordering;
	// generate Erasing and Requiring list
	// per fact, per SCC, gives a list of all E/R as a pair: <operator,position_in_scc>
	std::map<FactPair,std::vector< std::vector<std::pair<int,int>>  >> erasingList;
	std::map<FactPair,std::vector< std::vector<std::pair<int,int>>  >> requiringList;

	void exists_step_restriction(std::vector<int> & operator_variables, int time);
	void generateChain(std::vector<int> & operator_variables,
		    const std::vector<std::pair<int, int>>& E, const std::vector<std::pair<int, int>>& R, int time);

	
	int curClauseNumber;
	std::map<std::string,int> clauseCounter;
	std::map<std::string,int> variableCounter;
	
	void set_up_axioms();
	void set_up_exists_step();
	void set_up_single_step();

	std::pair<std::vector<FactPair>, std::vector<FactPair> > compute_needs_and_deletes_for_operator(int op);

	
	void generate_operator_variables(int time);
	void generate_fact_variables(int time);
	void generate_derived_predicate_variables(int time);
	void encode_direct_preconditions_and_effects_of_action(int time,
		std::map<FactPair, std::map<std::set<int>,std::vector<int>>> conditionBuffer,
		std::map<FactPair, std::map<std::set<int>, int>> conditionVariable
			);

public:
    mutable utils::LogProxy log;
	
	KautzSelmanRintanenEncoding(
			int _encoding,
			int	_disablingThreshold,
			bool _aboveThresholdGroupJoining,
			std::shared_ptr<sat_capsule> capsule, const TaskProxy _task_proxy, bool forceAtLeastOneAction,
    		utils::LogProxy _log);


	void encode(int fromTime, int toTime) override;
	void encodeInit(int fromTime, bool retractable) override;
	void encodeGoal(int toTime, bool retractable) override;
	void encodeStateEquals(int fromTime, int toTime, bool retractable) override;
	std::tuple<State,std::vector<State>,Plan> extractSolution(int initTime, std::vector<std::pair<int,int>> time_step_order) override;
	
	// functions for debugging
	void assertLabelsAtTime(int fromTime, std::set<int> labels) override;
};

//extern void add_sat_search_options_to_feature(plugins::Feature &feature, const std::string &description);
//extern std::tuple<OperatorCost, int, double, std::string, utils::Verbosity>
//get_sat_search_arguments_from_options(const plugins::Options &opts);
}

#endif
