import { createPreview } from "./api/preview.mjs";
import { installOpenTargetDetails } from "./Commands/open-target-details.mjs";
import { startGraphRuntime } from "./Commands/graph.mjs";
import { startInlinePreview } from "./Commands/inline-preview.mjs";
import { startRelationPanels } from "./Informal/Block/relation-panel.mjs";

export function startBlueprintPageRuntime(options = {}) {
  const preview = createPreview(options);
  installOpenTargetDetails(globalThis);
  startInlinePreview(preview);
  startRelationPanels(preview);
  startGraphRuntime(preview);
  return preview;
}

export const blueprintPageRuntime = startBlueprintPageRuntime();

export default {
  blueprintPageRuntime,
  startBlueprintPageRuntime,
};
