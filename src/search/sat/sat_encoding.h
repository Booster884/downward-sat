#ifndef SAT_SAT_ENCODING
#define SAT_SAT_ENCODING

#include "../task_proxy.h"
#include "../plan_manager.h"
#include "../utils/logging.h"
#include "../plugins/plugin.h"

//#include "sat_encoder.h"
//#include "../task_representation/fts_task.h"
//#include "../task_representation/transition_system.h"
//#include "../option_parser.h"


// needed for access to g_main_task
//#include "../globals.h"


namespace sat_search {

// abstract interface for a SAT encoding
class SATEncoding {
protected:
	std::shared_ptr<sat_capsule> sat;
    TaskProxy task_proxy;
	bool forceAtLeastOneAction;
public:
	SATEncoding(std::shared_ptr<sat_capsule> capsule, const TaskProxy _task_proxy, bool forceAtLeastOneAction) :
		sat(capsule), task_proxy(_task_proxy), forceAtLeastOneAction(forceAtLeastOneAction) {};
	virtual ~SATEncoding() = default;
	virtual void encode(int fromTime, int toTime) = 0;
	virtual void encodeInit(int fromTime, bool retractable) = 0;
	virtual void encodeGoal(int toTime, bool retractable) = 0;
	virtual void encodeStateEquals(int fromTime, int toTime, bool retractable) = 0;
	virtual std::tuple<State,std::vector<State>,Plan> extractSolution(int initTime, std::vector<std::pair<int,int>> time_step_order) = 0;
	
	// functions for debugging
	virtual void assertLabelsAtTime(int fromTime, std::set<int> labels) = 0;
};

// abstract interface for initialisation of SAT encoding
class SATEncodingFactory {
protected:
	std::shared_ptr<TaskProxy> task_proxy;
    std::shared_ptr<utils::LogProxy> log;
	const bool forceAtLeastOneAction;
public:
	SATEncodingFactory(bool _forceAtLeastOneAction) : forceAtLeastOneAction(_forceAtLeastOneAction) {};
	virtual ~SATEncodingFactory() = default;
	virtual std::unique_ptr<SATEncoding> createEncodingInstance(std::shared_ptr<sat_capsule> capsule) = 0;
	virtual void initialize(const TaskProxy _task_proxy, utils::LogProxy _log) = 0;
};

}

#endif
