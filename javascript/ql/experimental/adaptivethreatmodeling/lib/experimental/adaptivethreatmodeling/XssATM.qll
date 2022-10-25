/**
 * For internal use only.
 *
 * Defines shared code used by the XSS boosted query.
 */

private import semmle.javascript.heuristics.SyntacticHeuristics
private import semmle.javascript.security.dataflow.DomBasedXssCustomizations as Classic
import AdaptiveThreatModeling as ATM
private import StandardEndpointLabels as StandardEndpointLabels

/**
 * This module provides logic to filter candidate sinks to those which are likely XSS sinks.
 */
module SinkEndpointFilter {
  private import javascript
  private import Classic::DomBasedXss

  /**
   * Provides a set of reasons why a given data flow node should be excluded as a sink candidate.
   *
   * If this predicate has no results for a sink candidate `n`, then we should treat `n` as an
   * effective sink.
   */
  string getAReasonSinkExcluded(DataFlow::Node sinkCandidate) {
    result =
      any(StandardEndpointLabels::Labels::EndpointLabeller l |
        l instanceof StandardEndpointLabels::Labels::LegacyReasonSinkExcludedEndpointLabeller
      ).getLabel(sinkCandidate)
    or
    any(StandardEndpointLabels::Labels::LegacyArgToEndpointLabeller l).getLabel(sinkCandidate) =
      "legacy/arg-to/setState" and
    result = "setState calls ought to be safe in react applications"
    or
    // Require XSS sink candidates to be (a) arguments to external library calls (possibly
    // indirectly), or (b) heuristic sinks.
    //
    // Heuristic sinks are copied from the `HeuristicDomBasedXssSink` class defined within
    // `codeql/javascript/ql/src/semmle/javascript/heuristics/AdditionalSinks.qll`.
    // We can't reuse the class because importing that file would cause us to treat these
    // heuristic sinks as known sinks.
    not exists(
      any(StandardEndpointLabels::Labels::LegacyFlowsToLikelyExternalLibraryCallEndpointLabeller l)
          .getLabel(sinkCandidate)
    ) and
    not (
      isAssignedToOrConcatenatedWith(sinkCandidate, "(?i)(html|innerhtml)")
      or
      isArgTo(sinkCandidate, "(?i)(html|render)")
      or
      sinkCandidate instanceof StringOps::HtmlConcatenationLeaf
      or
      isConcatenatedWithStrings("(?is).*<[a-z ]+.*", sinkCandidate, "(?s).*>.*")
      or
      // In addition to the heuristic sinks from `HeuristicDomBasedXssSink`, explicitly allow
      // property writes like `elem.innerHTML = <TAINT>` that may not be picked up as HTML
      // concatenation leaves.
      exists(DataFlow::PropWrite pw |
        pw.getPropertyName().regexpMatch("(?i).*html*") and
        pw.getRhs() = sinkCandidate
      )
    ) and
    result = "not a direct argument to a likely external library call or a heuristic sink"
  }
}

class DomBasedXssAtmConfig extends ATM::AtmConfig {
  DomBasedXssAtmConfig() { this = "DomBasedXssATMConfig" }

  override predicate isKnownSource(DataFlow::Node source) { source instanceof Classic::DomBasedXss::Source }

  override predicate isKnownSink(DataFlow::Node sink) { sink instanceof Classic::DomBasedXss::Sink }

  override predicate isEffectiveSink(DataFlow::Node sinkCandidate) {
    not exists(SinkEndpointFilter::getAReasonSinkExcluded(sinkCandidate))
  }

  override ATM::EndpointType getASinkEndpointType() { result instanceof ATM::XssSinkType }
}

/**
 * A taint-tracking configuration for reasoning about XSS vulnerabilities.
 *
 * This is largely a copy of the taint tracking configuration for the standard XSSThroughDom query,
 * except additional ATM sinks have been added to the `isSink` predicate.
 */
class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "DomBasedXssATMConfiguration" }

  override predicate isSource(DataFlow::Node source) { source instanceof Classic::DomBasedXss::Source }

  override predicate isSink(DataFlow::Node sink) {
    sink instanceof Classic::DomBasedXss::Sink or
    any(DomBasedXssAtmConfig cfg).isEffectiveSink(sink)
  }

  override predicate isSanitizer(DataFlow::Node node) {
    super.isSanitizer(node) or
    node instanceof Classic::DomBasedXss::Sanitizer
  }

  override predicate isSanitizerGuard(TaintTracking::SanitizerGuardNode guard) {
    guard instanceof PrefixStringSanitizerActivated or
    guard instanceof QuoteGuard or
    guard instanceof ContainsHtmlGuard
  }

  override predicate isSanitizerEdge(DataFlow::Node pred, DataFlow::Node succ) {
    Classic::DomBasedXss::isOptionallySanitizedEdge(pred, succ)
  }
}

private import semmle.javascript.security.dataflow.Xss::Shared as Shared

private class PrefixStringSanitizerActivated extends TaintTracking::SanitizerGuardNode,
  Classic::DomBasedXss::PrefixStringSanitizer {
  PrefixStringSanitizerActivated() { this = this }
}

private class PrefixStringActivated extends DataFlow::FlowLabel, Classic::DomBasedXss::PrefixString {
  PrefixStringActivated() { this = this }
}

private class QuoteGuard extends TaintTracking::SanitizerGuardNode, Shared::QuoteGuard {
  QuoteGuard() { this = this }
}

private class ContainsHtmlGuard extends TaintTracking::SanitizerGuardNode, Shared::ContainsHtmlGuard {
  ContainsHtmlGuard() { this = this }
}
