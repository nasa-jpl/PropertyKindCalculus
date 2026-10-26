import {
  dataApiModuleUrl as coreDataApiModuleUrl,
  dataUrl as coreDataUrl,
  graphApiModuleUrl as coreGraphApiModuleUrl,
  htmlCacheUrl as coreHtmlCacheUrl,
  manifestUrl as coreManifestUrl,
  previewApiModuleUrl as corePreviewApiModuleUrl,
  previewKey as corePreviewKey,
  statementPreviewKey as coreStatementPreviewKey,
  version
} from "./blueprint-preview-core.mjs";

export { version };

export function optionsWithDefaultDataBaseUrl(options, moduleUrl) {
  const opts = options && typeof options === "object" ? Object.assign({}, options) : {};
  if (typeof opts.dataBaseUrl !== "string") {
    opts.dataBaseUrl = moduleUrl;
  }
  return opts;
}

export function createDefaultApiHandle(createApi) {
  let defaultApi = null;

  function readDefaultApi() {
    if (!defaultApi) {
      defaultApi = createApi();
    }
    return defaultApi;
  }

  function currentApi() {
    return defaultApi;
  }

  function getApi() {
    return Promise.resolve(readDefaultApi());
  }

  return {
    readDefaultApi,
    currentApi,
    getApi,
    ready: getApi()
  };
}

export function createPreviewUrlApi(moduleUrl) {
  const defaultBaseUrl = typeof moduleUrl === "string" ? moduleUrl : "";
  return {
    dataUrl: function (filename, baseUrl = defaultBaseUrl) {
      return coreDataUrl(filename, baseUrl);
    },
    manifestUrl: function (baseUrl = defaultBaseUrl) {
      return coreManifestUrl(baseUrl);
    },
    htmlCacheUrl: function (baseUrl = defaultBaseUrl) {
      return coreHtmlCacheUrl(baseUrl);
    },
    graphApiModuleUrl: function (baseUrl = defaultBaseUrl) {
      return coreGraphApiModuleUrl(baseUrl);
    },
    dataApiModuleUrl: function (baseUrl = defaultBaseUrl) {
      return coreDataApiModuleUrl(baseUrl);
    },
    previewApiModuleUrl: function (baseUrl = defaultBaseUrl) {
      return corePreviewApiModuleUrl(baseUrl);
    },
    previewKey: corePreviewKey,
    statementPreviewKey: coreStatementPreviewKey
  };
}

export function fallbackStoreStatus(url) {
  return {
    state: "idle",
    attempts: 0,
    url: url,
    lastError: "",
    entryCount: 0
  };
}

export function callDefaultApiSync(readDefaultApi, name, fallback, args) {
  const api = readDefaultApi();
  const method = api && api[name];
  if (typeof method === "function") {
    return method.apply(api, args || []);
  }
  return typeof fallback === "function" ? fallback() : fallback;
}

export async function callDefaultApi(readDefaultApi, apiKind, name, args) {
  const api = readDefaultApi();
  const method = api && api[name];
  if (typeof method !== "function") {
    throw new Error("Blueprint " + apiKind + " API method unavailable: " + name);
  }
  return method.apply(api, args);
}

export const blueprintApiCommon = {
  version,
  optionsWithDefaultDataBaseUrl,
  createDefaultApiHandle,
  createPreviewUrlApi,
  fallbackStoreStatus,
  callDefaultApiSync,
  callDefaultApi
};

export default blueprintApiCommon;
