/**
 * For internal use only.
 *
 * Configures boosting for adaptive threat modeling (ATM).
 */

private import java as java
private import semmle.code.java.dataflow.TaintTracking
import EndpointTypes
import EndpointCharacteristics as EndpointCharacteristics

/**
 * EXPERIMENTAL. This API may change in the future.
 *
 * A configuration class for defining known endpoints and endpoint filters for adaptive threat
 * modeling (ATM). Each boosted query must define its own extension of this abstract class.
 *
 * A configuration defines a set of known sources (`isKnownSource`) and sinks (`isKnownSink`).
 * It must also define a sink endpoint filter (`isEffectiveSink`) that filters candidate sinks
 * predicted by the machine learning model to a set of effective sinks.
 *
 * To get started with ATM, you can copy-paste an implementation of the relevant predicates from a
 * `DataFlow::Configuration` or `TaintTracking::Configuration` class for a standard security query.
 * For example, for SQL injection you can start by defining the `isKnownSource` and `isKnownSink`
 * predicates in the ATM configuration by copying and pasting the implementations of `isSource` and
 * `isSink` from `SqlInjection::Configuration`.
 *
 * Note that if the security query configuration defines additional edges beyond the standard data
 * flow edges, such as `NosqlInjection::Configuration`, you may need to replace the definition of
 * `isAdditionalFlowStep` with a more generalised definition of additional edges. See
 * `NosqlInjectionATM.qll` for an example of doing this.
 */
abstract class AtmConfig extends TaintTracking::Configuration {
  bindingset[this]
  AtmConfig() { any() }

  /**
   * Holds if `source` is a relevant taint source. When sources are not boosted, `isSource` is equivalent to
   * `isKnownSource` (i.e there are no "effective" sources to be classified by an ML model).
   */
  override predicate isSource(DataFlow::Node source) { this.isKnownSource(source) }

  /**
   * Holds if `sink` is a known taint sink or an "effective" sink (a candidate to be classified by an ML model).
   */
  override predicate isSink(DataFlow::Node sink) {
    this.isKnownSink(sink) or this.isEffectiveSink(sink)
  }

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * Holds if `source` is a known source of flow.
   */
  abstract predicate isKnownSource(DataFlow::Node source);

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * Holds if `sink` is a known sink of for this query
   */
  final predicate isKnownSink(DataFlow::Node sink) {
    // If the list of characteristics includes positive indicators with maximal confidence for this class, then it's a
    // known sink for the class.
    isKnownSink(sink, this.getASinkEndpointType())
  }

  /**
   * Holds if `sink` is a known sink for this query of type `sinkType`.
   */
  final predicate isKnownSink(DataFlow::Node sink, EndpointType sinkType) {
    sinkType = this.getASinkEndpointType() and
    // If the list of characteristics includes positive indicators with maximal confidence for this class, then it's a
    // known sink for the class.
    exists(EndpointCharacteristics::EndpointCharacteristic characteristic |
      characteristic.appliesToEndpoint(sink) and
      characteristic.hasImplications(sinkType, true, characteristic.maximalConfidence())
    )
  }

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * Holds if the candidate source `candidateSource` predicted by the machine learning model should be
   * an effective source, i.e. one considered as a possible source of flow in the boosted query.
   */
  predicate isEffectiveSource(DataFlow::Node candidateSource) { none() }

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * Holds if the candidate sink `candidateSink` predicted by the machine learning model should be
   * an effective sink, i.e. one considered as a possible sink of flow in the boosted query.
   */
  predicate isEffectiveSink(DataFlow::Node candidateSink) {
    not exists(this.getAReasonSinkExcluded(candidateSink))
  }

  /**
   * Gets the list of characteristics that cause `candidateSink` to be excluded as an effective sink.
   */
  final EndpointCharacteristics::EndpointCharacteristic getAReasonSinkExcluded(
    DataFlow::Node candidateSink
  ) {
    // An endpoint is an effective sink (sink candidate) if none of its characteristics give much indication whether or
    // not it is a sink. Historically, we used endpoint filters, and scored endpoints that are filtered out neither by
    // a standard endpoint filter nor by an endpoint filter specific to this sink type.
    result.appliesToEndpoint(candidateSink) and
    // Exclude endpoints that have a characteristic that implies they're not sinks for _any_ sink type.
    exists(float confidence |
      confidence >= result.mediumConfidence() and
      result.hasImplications(any(NegativeSinkType negative), true, confidence)
    )
    or
    // Exclude endpoints that have a characteristic that implies they're not sinks for _this particular_ sink type,
    // for every sink type relevant to this query.
    not exists(EndpointType sinkType |
      sinkType = this.getASinkEndpointType() and
      not exists(float confidence |
        confidence >= result.mediumConfidence() and
        result.hasImplications(sinkType, false, confidence)
      )
    )
  }

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * Get an endpoint type for the sources of this query. A query may have multiple applicable
   * endpoint types for its sources.
   */
  EndpointType getASourceEndpointType() { none() }

  /**
   * EXPERIMENTAL. This API may change in the future.
   *
   * Get all sink types that can be sinks for this query. A query may have multiple applicable
   * endpoint types for its sinks.
   */
  abstract EndpointType getASinkEndpointType();

  pragma[inline]
  predicate isFlowLikelyInBaseQuery(DataFlow::Node source, DataFlow::Node sink) {
    this.isKnownSource(source) and this.isKnownSink(sink)
  }

  /**
   * Holds if if `sink` is an effective sink with flow from `source` which gets used as a sink candidate for scoring
   * with the ML model.
   */
  predicate isSinkCandidateWithFlow(DataFlow::PathNode sink) {
    exists(DataFlow::PathNode source |
      // Note: In JavaScript there's no need to check `isEffectiveSink` here explicitly, because `hasFlowPath` calls `isSink` which
      // requires an endpoint to be either a known sink or an effective sink. Known sinks are later filtered out by
      // `isFlowLikelyInBaseQuery`, leaving only effective sinks.
      this.hasFlowPath(source, sink) and
      not this.isFlowLikelyInBaseQuery(source.getNode(), sink.getNode()) and
      isEffectiveSink(sink.getNode()) and
      not isKnownSink(sink.getNode()) // As long as we're not boosting sources this is already implicitly checked by `isFlowLikelyInBaseQuery`
    )
  }
}
