#include "sase.h"

#include "../plugins/plugin.h"

namespace plugin_sat {
class SaseEncodingFeature
    : public plugins::TypedFeature<
          sat_search::SATEncodingFactory, sat_search::SaseEncodingFactory> {
public:
    SaseEncodingFeature() : TypedFeature("sase") {
        document_title("SASE encoding by Huang et al");
        document_synopsis("");
        add_option<bool>(
            "forceAtLeastOneAction", "force at least one action per timestep",
            "true");
    }

    virtual std::shared_ptr<sat_search::SaseEncodingFactory> create_component(
        const plugins::Options &opts) const override {
        plugins::Options options_copy(opts);
        return plugins::make_shared_from_arg_tuples<
            sat_search::SaseEncodingFactory>(
            options_copy.get<bool>("forceAtLeastOneAction"));
    }
};

static plugins::FeaturePlugin<SaseEncodingFeature> _plugin;
}
