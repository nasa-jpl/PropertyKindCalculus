function defaultGlobalScope() {
  return typeof globalThis !== "undefined" ? globalThis : window;
}

export function openTargetDetailsFromHash(globalScope = defaultGlobalScope()) {
  const windowObj = globalScope && globalScope.window ? globalScope.window : globalScope;
  const documentObj = windowObj.document;
  if (!windowObj.location || !windowObj.location.hash || !documentObj) return;
  const id = decodeURIComponent(windowObj.location.hash.slice(1));
  if (!id) return;
  const target = documentObj.getElementById(id);
  if (!target) return;
  const details = target.matches("details") ? target : target.closest("details");
  if (details) details.open = true;
}

export function installOpenTargetDetails(globalScope = defaultGlobalScope()) {
  const windowObj = globalScope && globalScope.window ? globalScope.window : globalScope;
  const documentObj = windowObj.document;
  if (!documentObj) return;
  const openFromHash = function () {
    openTargetDetailsFromHash(windowObj);
  };
  if (documentObj.readyState === "loading") {
    documentObj.addEventListener("DOMContentLoaded", openFromHash);
  } else {
    openFromHash();
  }
  windowObj.addEventListener("hashchange", openFromHash);
}

export const openTargetDetails = {
  openTargetDetailsFromHash,
  installOpenTargetDetails
};

export default openTargetDetails;
