import javascript
import experimental.adaptivethreatmodeling.StandardEndpointFilters

DataFlow::CallNode getALikelyExternalLibraryCall() {
    getAnEndpointLabel(result) = "legacy/likely-external-library-call"
}

select getALikelyExternalLibraryCall()
