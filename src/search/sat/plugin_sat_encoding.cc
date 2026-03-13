#include "kautz_selman_rintanen.h"
#include "../plugins/plugin.h"

using namespace std;

namespace plugin_sat {

	
static class SATEncodingFactoryCategoryPlugin : public plugins::TypedCategoryPlugin<sat_search::SATEncodingFactory> {
	public:
	    SATEncodingFactoryCategoryPlugin () : TypedCategoryPlugin("SATEncodingFactory") {
	        document_synopsis(
	            "This page describes available SAT encodings.");
	    }
	}
	_category_plugin;


};
