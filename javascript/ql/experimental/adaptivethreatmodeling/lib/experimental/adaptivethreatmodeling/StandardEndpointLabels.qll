/**
 * For internal use only.
 *
 * Provides classes and predicates that are useful for labelling endpoints.
 *
 * The standard use of this library is to make use of `isPotentialEffectiveSink/1`
 */

private import javascript
private import semmle.javascript.filters.ClassifyFiles as ClassifyFiles
private import CoreKnowledge as CoreKnowledge
private import StandardEndpointFilters as StandardEndpointFilters

module Labels {
  private newtype TEndpointLabeller =
    TLegacyArgToEndpointLabeller() or
    TLegacyFlowsToLikelyExternalLibraryCallEndpointLabeller() or
    TLegacyIsLikelyExternalLibraryCallEndpointLabeller() or
    TLegacyModeledDbAccess() or
    TLegacyModeledHttp(string kind) { kind = ["request", "response"] } or
    TLegacyModeledSink() or
    TLegacyModeledStepSource() or
    TLegacyReasonSinkExcludedEndpointLabeller(string innerReason) {
      innerReason =
        "legacy/reason-sink-excluded/" +
          [
            "argument to modeled function", //
            "argument to sinkless library", //
            "sanitizer", //
            "predicate", //
            "hash", //
            "numeric", //
            "in " + ["externs", "generated", "library", "test"] + " file" //
          ]
    }

  /**
   * An endpoint labeller defines logic that labels a subset of endpoints.
   *
   * Each instance of an endpoint labeller is claiming a range of endpoints (that range is defined by the `toString` method).
   * It may then label endpoints within that range, but not outside of that range.
   *
   * The EndpointLabelsAreInRange.ql query checks that this invariant is upheld.
   */
  class EndpointLabeller extends TEndpointLabeller {
    abstract string getLabel(DataFlow::Node n);

    abstract string getRange();

    string toString() { result = getRange() }
  }

  class LegacyArgToEndpointLabeller extends EndpointLabeller, TLegacyArgToEndpointLabeller {
    override string getLabel(DataFlow::Node n) {
      exists(DataFlow::InvokeNode call | n = call.getAnArgument() |
        result = "legacy/arg-to/" + call.getCalleeName()
      )
    }

    override string getRange() { result = "legacy/arg-to/**" }
  }

  class LegacyFlowsToLikelyExternalLibraryCallEndpointLabeller extends EndpointLabeller,
    TLegacyFlowsToLikelyExternalLibraryCallEndpointLabeller {
    override string getLabel(DataFlow::Node n) {
      StandardEndpointFilters::flowsToArgumentOfLikelyExternalLibraryCall(n) and
      result = "legacy/likely-external-library-call/flows-to"
    }

    override string getRange() { result = "legacy/likely-external-library-call/flows-to" }
  }

  class LegacyIsLikelyExternalLibraryCallEndpointLabeller extends EndpointLabeller,
    TLegacyIsLikelyExternalLibraryCallEndpointLabeller {
    override string getLabel(DataFlow::Node n) {
      n = StandardEndpointFilters::getALikelyExternalLibraryCall() and
      result = "legacy/likely-external-library-call/is"
    }

    override string getRange() { result = "legacy/likely-external-library-call/is" }
  }

  class LegacyModeledDbAccessEndpointLabeller extends EndpointLabeller, TLegacyModeledDbAccess {
    override string getLabel(DataFlow::Node n) {
      exists(DataFlow::CallNode call | n = call.getAnArgument() |
        call.(DataFlow::MethodCallNode).getMethodName() =
          ["create", "createCollection", "createIndexes"] and
        result = "legacy/modeled/db-access/matches database access call heuristic"
        or
        call instanceof DatabaseAccess and
        result = "legacy/modeled/db-access/classic-model"
      )
    }

    override string getRange() { result = "legacy/modeled/db-access/**" }
  }

  class LegacyModeledHttpEndpointLabeller extends Labels::EndpointLabeller, TLegacyModeledHttp {
    string kind;

    LegacyModeledHttpEndpointLabeller() { this = TLegacyModeledHttp(kind) }

    override string getLabel(DataFlow::Node n) {
      exists(DataFlow::CallNode call | n = call.getAnArgument() |
        kind = "request" and
        call.getReceiver() instanceof Http::RequestNode and
        result = "legacy/modeled/http/request"
        or
        kind = "response" and
        call.getReceiver() instanceof Http::ResponseNode and
        result = "legacy/modeled/http/response"
      )
    }

    override string getRange() { result = "legacy/modeled/http/" + kind }
  }

  class LegacyModeledSinkEndpointLabeller extends Labels::EndpointLabeller, TLegacyModeledSink {
    override string getLabel(DataFlow::Node n) {
      CoreKnowledge::isArgumentToKnownLibrarySinkFunction(n) and
      result = "legacy/modeled/sink"
    }

    override string getRange() { result = "legacy/modeled/sink" }
  }

  class LegacyModeledStepSourceEndpointLabeller extends Labels::EndpointLabeller,
    TLegacyModeledStepSource {
    override string getLabel(DataFlow::Node n) {
      CoreKnowledge::isKnownStepSrc(n) and
      result = "legacy/modeled/step-source"
    }

    override string getRange() { result = "legacy/modeled/step-source" }
  }

  class LegacyReasonSinkExcludedEndpointLabeller extends EndpointLabeller,
    TLegacyReasonSinkExcludedEndpointLabeller {
    override string getLabel(DataFlow::Node n) {
      exists(string inner |
        this = TLegacyReasonSinkExcludedEndpointLabeller(inner) and
        inner = StandardEndpointFilters::getAReasonSinkExcluded(n)
      |
        result = inner
      )
    }

    override string getRange() {
      exists(string inner | this = TLegacyReasonSinkExcludedEndpointLabeller(inner) |
        result = inner
      )
    }
  }
}

string getAnEndpointLabel(DataFlow::Node n) { result = any(Labels::EndpointLabeller l).getLabel(n) }

DataFlow::Node getALabeledEndpoint(string label) { getAnEndpointLabel(result) = label }
