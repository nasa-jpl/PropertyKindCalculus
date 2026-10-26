import { normalizePanelBehavior, readElementOption, readFunctionOption, readNumberOption, readObjectOption, readRootOption, readStringOption } from "./preview-runtime-base.mjs";

  // Bundled preview lifecycle helpers.
  //
  // These helpers bind close buttons, popovers, trigger lifetimes,
  // dismissal, repositioning, and keep-open checks for bundled clients.

  export function bindCloseOnce(button, onClose) {
    if (!(button instanceof Element)) return;
    if (button.getAttribute("data-bp-bound") === "1") return;
    if (typeof onClose !== "function") return;
    button.setAttribute("data-bp-bound", "1");
    button.addEventListener("click", function (ev) {
      ev.preventDefault();
      ev.stopPropagation();
      onClose(ev);
    });
  }

  export function bindDismissHandlers(options) {
    const opts = options && typeof options === "object" ? options : {};
    const root = readElementOption(opts, "root", null);
    const trigger = readElementOption(opts, "trigger", null);
    const panel = readElementOption(opts, "panel", null);
    const closeButton = readElementOption(opts, "closeButton", null);
    const owner =
      opts.owner instanceof Element
        ? opts.owner
        : (trigger instanceof Element ? trigger : root);
    const boundAttr = readStringOption(opts, "boundAttr", "data-bp-dismiss-bound");
    const outsideEvent = readStringOption(opts, "outsideEvent", "click");
    const open = readFunctionOption(opts, "open", function () {});
    const close = readFunctionOption(opts, "close", function () {});
    const isOpen = readFunctionOption(opts, "isOpen", function () {
      return panel instanceof HTMLElement ? !panel.hidden : true;
    });
    const toggle = readFunctionOption(opts, "toggle", function () {
      if (isOpen()) {
        close();
      } else {
        open();
      }
    });
    const bindTrigger = opts.bindTrigger !== false && trigger instanceof Element;
    const bindOutside = opts.bindOutside !== false && root instanceof Element;
    const bindEscape = opts.bindEscape === true;
    const stopPanelClick = opts.stopPanelClick === true;
    const preventTriggerDefault = opts.preventTriggerDefault !== false;
    const stopTriggerClick = opts.stopTriggerClick !== false;
    const preventCloseDefault = opts.preventCloseDefault !== false;
    const stopCloseClick = opts.stopCloseClick !== false;

    const controller = {
      root: root,
      trigger: trigger,
      panel: panel,
      closeButton: closeButton,
      isOpen: isOpen,
      open: open,
      close: close,
      toggle: toggle
    };

    if (!(owner instanceof Element)) return controller;
    if (owner.getAttribute(boundAttr) === "1") return controller;
    owner.setAttribute(boundAttr, "1");

    if (bindTrigger) {
      trigger.addEventListener("click", function (ev) {
        if (preventTriggerDefault) ev.preventDefault();
        if (stopTriggerClick) ev.stopPropagation();
        toggle(ev);
      });
    }
    if (closeButton instanceof Element) {
      closeButton.addEventListener("click", function (ev) {
        if (preventCloseDefault) ev.preventDefault();
        if (stopCloseClick) ev.stopPropagation();
        close(ev);
      });
    }
    if (stopPanelClick && panel instanceof Element) {
      panel.addEventListener("click", function (ev) {
        ev.stopPropagation();
      });
    }
    if (bindOutside) {
      document.addEventListener(outsideEvent, function (ev) {
        if (!isOpen()) return;
        const target = ev.target;
        if (!(target instanceof Node)) {
          close(ev);
          return;
        }
        if (root.contains(target)) return;
        close(ev);
      });
    }
    if (bindEscape) {
      document.addEventListener("keydown", function (ev) {
        if (ev.key !== "Escape") return;
        if (!isOpen()) return;
        close(ev);
      });
    }

    return controller;
  }

  export function bindAnchoredPopover(options) {
    const opts = options && typeof options === "object" ? options : {};
    const root = readElementOption(opts, "root", null);
    const trigger = readElementOption(opts, "trigger", null);
    const panel = readElementOption(opts, "panel", null);
    const closeButton = readElementOption(opts, "close", null);
    const boundAttr = readStringOption(opts, "boundAttr", "data-bp-popover-bound");
    const offset = readNumberOption(opts, "offset", 8);
    const positionPopover = readFunctionOption(opts, "position", function (_controller, rootNode, triggerNode, panelNode) {
      if (!(rootNode instanceof Element)) return;
      if (!(triggerNode instanceof Element)) return;
      if (!(panelNode instanceof HTMLElement)) return;
      const rootRect = rootNode.getBoundingClientRect();
      const triggerRect = triggerNode.getBoundingClientRect();
      const top = Math.max(0, Math.round(triggerRect.bottom - rootRect.top + offset));
      const right = Math.max(0, Math.round(rootRect.right - triggerRect.right));
      panelNode.style.top = top + "px";
      panelNode.style.right = right + "px";
    });

    if (!(root instanceof Element) || !(trigger instanceof Element) || !(panel instanceof HTMLElement)) {
      return null;
    }
    const panelElement = panel;

    const controller = {
      root: root,
      trigger: trigger,
      panel: panelElement,
      closeButton: closeButton,
      isOpen: function () { return !panelElement.hidden; },
      open: function () { setOpen(true); },
      close: function () { setOpen(false); },
      toggle: function () { setOpen(panelElement.hidden); },
      position: position,
      setOpen: setOpen
    };

    function position() {
      positionPopover(controller, root, trigger, panelElement);
    }

    function setOpen(isOpen) {
      const open = !!isOpen;
      if (open) position();
      panelElement.hidden = !open;
      trigger.setAttribute("aria-expanded", open ? "true" : "false");
    }

    setOpen(false);
    bindDismissHandlers({
      owner: trigger,
      root: root,
      trigger: trigger,
      panel: panelElement,
      close: controller.close,
      closeButton: closeButton,
      isOpen: controller.isOpen,
      toggle: controller.toggle,
      boundAttr: boundAttr,
      outsideEvent: "pointerdown"
    });

    return controller;
  }

  export function readAnchorRect(anchor) {
    if (anchor instanceof Element) {
      return anchor.getBoundingClientRect();
    }
    if (
      anchor &&
      typeof anchor === "object" &&
      Number.isFinite(anchor.left) &&
      Number.isFinite(anchor.right) &&
      Number.isFinite(anchor.top) &&
      Number.isFinite(anchor.bottom)
    ) {
      return anchor;
    }
    return null;
  }

  export function positionAnchoredPanel(panel, anchor, margin, offset) {
    if (!(panel instanceof HTMLElement)) return;
    const rect = readAnchorRect(anchor);
    if (!rect) return;
    const safeMargin = Number.isFinite(margin) ? margin : 12;
    const safeOffset = Number.isFinite(offset) ? offset : 10;
    const panelRect = panel.getBoundingClientRect();
    const panelWidth = panelRect.width || Math.min(520, window.innerWidth - safeMargin * 2);
    const panelHeight = panelRect.height || Math.min(420, window.innerHeight - safeMargin * 2);
    let left = rect.left;
    if (left + panelWidth > window.innerWidth - safeMargin) {
      left = window.innerWidth - panelWidth - safeMargin;
    }
    left = Math.max(safeMargin, left);
    let top = rect.bottom + safeOffset;
    if (top + panelHeight > window.innerHeight - safeMargin) {
      top = rect.top - panelHeight - safeOffset;
    }
    top = Math.max(safeMargin, top);
    panel.style.left = left + "px";
    panel.style.top = top + "px";
  }

  export function bindPanelRepositioner(options) {
    const opts = options && typeof options === "object" ? options : {};
    const owner = readElementOption(opts, "owner", null);
    const boundAttr = readStringOption(opts, "boundAttr", "data-bp-panel-reposition-bound");
    const reposition = readFunctionOption(opts, "reposition", null);
    const bindResize = opts.bindResize !== false;
    const bindScroll = opts.bindScroll !== false;
    if (!reposition) return null;

    const controller = {
      reposition: function () {
        reposition(controller);
      }
    };

    if (owner instanceof Element) {
      if (owner.getAttribute(boundAttr) === "1") return controller;
      owner.setAttribute(boundAttr, "1");
    }
    if (bindResize) window.addEventListener("resize", controller.reposition);
    if (bindScroll) window.addEventListener("scroll", controller.reposition, true);
    return controller;
  }

  export function shouldKeepOpen(nextTarget, trigger, panel) {
    if (!(nextTarget instanceof Element)) return false;
    if (trigger instanceof Element && trigger.contains(nextTarget)) return true;
    if (panel instanceof Element && panel.contains(nextTarget)) return true;
    const inlinePanel = document.getElementById("bp-inline-preview-panel");
    if (inlinePanel instanceof Element && inlinePanel.contains(nextTarget)) return true;
    return false;
  }

  function eventKey(ev) {
    if (!ev || typeof ev !== "object" || !("key" in ev)) return "";
    const key = ev.key;
    return typeof key === "string" ? key : "";
  }

  export function bindPreviewTriggers(options) {
    const opts = options && typeof options === "object" ? options : {};
    const triggerRoot = readRootOption(opts, "triggerRoot", document);
    const eventRoot = readRootOption(opts, "eventRoot", null);
    const panel = readElementOption(opts, "panel", null);
    const triggerSelector = readStringOption(opts, "triggerSelector", "");
    const triggerBoundAttr = readStringOption(
      opts,
      "triggerBoundAttr",
      "data-bp-preview-trigger-bound"
    );
    const eventRootBoundAttr = readStringOption(
      opts,
      "eventRootBoundAttr",
      "data-bp-preview-events-bound"
    );
    const panelBoundAttr = readStringOption(
      opts,
      "panelBoundAttr",
      "data-bp-preview-panel-lifetime-bound"
    );
    const defaults = readObjectOption(opts, "defaults", {});
    const behaviorSource = readObjectOption(opts, "behavior", null);
    const readBehavior = readFunctionOption(opts, "getBehavior", function () {
      return behaviorSource;
    });
    const show = readFunctionOption(opts, "show", function () {});
    const hide = readFunctionOption(opts, "hide", function () {});
    const position = readFunctionOption(opts, "position", function () {});
    const filterTrigger = readFunctionOption(opts, "filterTrigger", function () { return true; });
    const getActiveTrigger = readFunctionOption(opts, "getActiveTrigger", function () {
      return null;
    });
    const getActiveAnchor = readFunctionOption(opts, "getActiveAnchor", getActiveTrigger);
    const resolveTriggerOption = readFunctionOption(opts, "resolveTrigger", null);
    const shouldKeepPreviewOpen = readFunctionOption(opts, "shouldKeepOpen", null);
    const onLeave = readFunctionOption(opts, "onLeave", null);
    const onPanelEnter = readFunctionOption(opts, "onPanelEnter", null);
    const onPanelLeave = readFunctionOption(opts, "onPanelLeave", null);
    const hideDelay = readNumberOption(opts, "hideDelay", 180);
    const bindPanel = opts.bindPanel !== false;
    const bindEscape = opts.bindEscape !== false;
    const bindWindow = opts.bindWindow !== false;
    const activateOnClick = opts.activateOnClick === true;
    const activateOnKeydown = opts.activateOnKeydown === true;
    const enterRequiresHover = opts.enterRequiresHover === true;
    let hideTimer = null;

    function behavior() {
      return normalizePanelBehavior(panel, defaults, readBehavior());
    }

    function cancelHide() {
      if (hideTimer !== null) {
        clearTimeout(hideTimer);
        hideTimer = null;
      }
    }

    function hideNow() {
      cancelHide();
      hide();
    }

    function scheduleHide() {
      cancelHide();
      const current = behavior();
      if (!current.isHover) {
        hideNow();
        return;
      }
      hideTimer = window.setTimeout(function () {
        hideTimer = null;
        hide();
      }, hideDelay);
    }

    const controls = {
      cancelHide: cancelHide,
      scheduleHide: scheduleHide,
      hide: hideNow,
      behavior: behavior
    };

    /**
     * @param {unknown} target
     * @param {unknown} ev
     * @returns {Element | null}
     */
    function resolveTrigger(target, ev) {
      if (resolveTriggerOption) {
        const resolved = resolveTriggerOption(target, ev);
        return resolved instanceof Element ? resolved : null;
      }
      const element = target instanceof Element ? target : null;
      if (!element) return null;
      if (!triggerSelector) return element;
      if (element.matches(triggerSelector)) return element;
      const closest = Element.prototype.closest.call(element, triggerSelector);
      return closest instanceof Element ? closest : null;
    }

    function keepOpen(trigger, ev) {
      if (shouldKeepPreviewOpen && shouldKeepPreviewOpen(trigger, ev, controls)) return true;
      return shouldKeepOpen(ev && ev.relatedTarget, trigger, panel);
    }

    function showTrigger(trigger, ev, force) {
      if (!(trigger instanceof Element)) return;
      if (!filterTrigger(trigger, ev, controls)) return;
      if (!force && enterRequiresHover && !behavior().isHover) return;
      cancelHide();
      show(trigger, ev, controls);
    }

    function leaveTrigger(trigger, ev) {
      if (!(trigger instanceof Element)) return;
      if (!filterTrigger(trigger, ev, controls)) return;
      const current = behavior();
      if (!current.isHover) return;
      if (onLeave && onLeave(trigger, ev, controls)) return;
      if (keepOpen(trigger, ev)) return;
      scheduleHide();
    }

    function activateTrigger(trigger, ev) {
      if (!(trigger instanceof Element)) return;
      if (!filterTrigger(trigger, ev, controls)) return;
      const current = behavior();
      if (!current.isPinned) return;
      showTrigger(trigger, ev, true);
      if (ev && typeof ev.preventDefault === "function") ev.preventDefault();
    }

    function bindDirectTrigger(trigger) {
      if (!(trigger instanceof Element)) return;
      if (!filterTrigger(trigger, null, controls)) return;
      if (trigger.getAttribute(triggerBoundAttr) === "1") return;
      trigger.setAttribute(triggerBoundAttr, "1");
      trigger.addEventListener("mouseenter", function (ev) {
        showTrigger(trigger, ev);
      });
      trigger.addEventListener("focusin", function (ev) {
        showTrigger(trigger, ev);
      });
      trigger.addEventListener("mouseleave", function (ev) {
        leaveTrigger(trigger, ev);
      });
      trigger.addEventListener("focusout", function (ev) {
        leaveTrigger(trigger, ev);
      });
      if (activateOnClick) {
        trigger.addEventListener("click", function (ev) {
          activateTrigger(trigger, ev);
        });
      }
      if (activateOnKeydown) {
        trigger.addEventListener("keydown", function (ev) {
          const key = eventKey(ev);
          if (key !== "Enter" && key !== " ") return;
          activateTrigger(trigger, ev);
        });
      }
    }

    function bindDelegatedRoot(root) {
      if (!(root instanceof Element || root instanceof Document)) return;
      if (root instanceof Element) {
        if (root.getAttribute(eventRootBoundAttr) === "1") return;
        root.setAttribute(eventRootBoundAttr, "1");
      }
      root.addEventListener("mouseover", function (ev) {
        showTrigger(resolveTrigger(ev.target, ev), ev);
      });
      root.addEventListener("focusin", function (ev) {
        showTrigger(resolveTrigger(ev.target, ev), ev);
      });
      root.addEventListener("mouseout", function (ev) {
        leaveTrigger(resolveTrigger(ev.target, ev), ev);
      });
      root.addEventListener("focusout", function (ev) {
        leaveTrigger(resolveTrigger(ev.target, ev), ev);
      });
      if (activateOnClick) {
        root.addEventListener("click", function (ev) {
          activateTrigger(resolveTrigger(ev.target, ev), ev);
        });
      }
      if (activateOnKeydown) {
        root.addEventListener("keydown", function (ev) {
          const key = eventKey(ev);
          if (key !== "Enter" && key !== " ") return;
          activateTrigger(resolveTrigger(ev.target, ev), ev);
        });
      }
    }

    function bindPanelLifetime() {
      if (!bindPanel || !(panel instanceof Element)) return;
      if (panel.getAttribute(panelBoundAttr) === "1") return;
      panel.setAttribute(panelBoundAttr, "1");
      const enterPanel = function (ev) {
        cancelHide();
        if (onPanelEnter) onPanelEnter(panel, ev, controls);
      };
      const leavePanel = function (ev) {
        const current = behavior();
        if (!current.isHover) return;
        if (onPanelLeave && onPanelLeave(panel, ev, controls)) return;
        if (shouldKeepOpen(ev && ev.relatedTarget, getActiveAnchor(), panel)) return;
        scheduleHide();
      };
      panel.addEventListener("mouseenter", enterPanel);
      panel.addEventListener("focusin", enterPanel);
      panel.addEventListener("mouseleave", leavePanel);
      panel.addEventListener("focusout", leavePanel);
    }

    function refresh(root) {
      const scope = root instanceof Element || root instanceof Document ? root : triggerRoot;
      if (eventRoot) {
        bindDelegatedRoot(eventRoot);
        return;
      }
      if (!triggerSelector || !(scope instanceof Element || scope instanceof Document)) return;
      if (scope instanceof Element && scope.matches(triggerSelector)) {
        bindDirectTrigger(scope);
      }
      scope.querySelectorAll(triggerSelector).forEach(bindDirectTrigger);
    }

    bindPanelLifetime();
    refresh(triggerRoot);

    if (bindEscape) {
      document.addEventListener("keydown", function (ev) {
        if (ev.key === "Escape") hideNow();
      });
    }
    if (bindWindow) {
      bindPanelRepositioner({
        reposition: function () {
          const current = behavior();
          const activeAnchor = getActiveAnchor();
          if (current.isAnchored && activeAnchor && panel instanceof HTMLElement && !panel.hidden) {
            position(activeAnchor);
          }
        }
      });
    }

    return Object.assign(controls, {
      refresh: refresh,
      showTrigger: showTrigger
    });
  }

  export const previewRuntimeLifecycle = {
    bindCloseOnce,
    bindDismissHandlers,
    bindAnchoredPopover,
    readAnchorRect,
    positionAnchoredPanel,
    bindPanelRepositioner,
    shouldKeepOpen,
    bindPreviewTriggers
  };

export default previewRuntimeLifecycle;
