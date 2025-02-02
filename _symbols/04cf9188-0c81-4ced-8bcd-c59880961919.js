// New Block - Updated February 2, 2025
function noop() { }
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function create_slot(definition, ctx, $$scope, fn) {
    if (definition) {
        const slot_ctx = get_slot_context(definition, ctx, $$scope, fn);
        return definition[0](slot_ctx);
    }
}
function get_slot_context(definition, ctx, $$scope, fn) {
    return definition[1] && fn
        ? assign($$scope.ctx.slice(), definition[1](fn(ctx)))
        : $$scope.ctx;
}
function get_slot_changes(definition, $$scope, dirty, fn) {
    if (definition[2] && fn) {
        const lets = definition[2](fn(dirty));
        if ($$scope.dirty === undefined) {
            return lets;
        }
        if (typeof lets === 'object') {
            const merged = [];
            const len = Math.max($$scope.dirty.length, lets.length);
            for (let i = 0; i < len; i += 1) {
                merged[i] = $$scope.dirty[i] | lets[i];
            }
            return merged;
        }
        return $$scope.dirty | lets;
    }
    return $$scope.dirty;
}
function update_slot_base(slot, slot_definition, ctx, $$scope, slot_changes, get_slot_context_fn) {
    if (slot_changes) {
        const slot_context = get_slot_context(slot_definition, ctx, $$scope, get_slot_context_fn);
        slot.p(slot_context, slot_changes);
    }
}
function get_all_dirty_from_scope($$scope) {
    if ($$scope.ctx.length > 32) {
        const dirty = [];
        const length = $$scope.ctx.length / 32;
        for (let i = 0; i < length; i++) {
            dirty[i] = -1;
        }
        return dirty;
    }
    return -1;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function compute_rest_props(props, keys) {
    const rest = {};
    keys = new Set(keys);
    for (const k in props)
        if (!keys.has(k) && k[0] !== '$')
            rest[k] = props[k];
    return rest;
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function stop_propagation(fn) {
    return function (event) {
        event.stopPropagation();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_input_value(input, value) {
    input.value = value == null ? '' : value;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function get_spread_object(spread_props) {
    return typeof spread_props === 'object' && spread_props !== null ? spread_props : {};
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/**
 * @license lucide-svelte v0.474.0 - ISC
 *
 * ISC License
 * 
 * Copyright (c) for portions of Lucide are held by Cole Bemis 2013-2022 as part of Feather (MIT). All other copyright (c) for Lucide are held by Lucide Contributors 2022.
 * 
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 * 
 */
const defaultAttributes = {
    xmlns: 'http://www.w3.org/2000/svg',
    width: 24,
    height: 24,
    viewBox: '0 0 24 24',
    fill: 'none',
    stroke: 'currentColor',
    'stroke-width': 2,
    'stroke-linecap': 'round',
    'stroke-linejoin': 'round',
};

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i][0];
	child_ctx[12] = list[i][1];
	return child_ctx;
}

// (35:4) <svelte:element this={tag} {...attrs}/>
function create_dynamic_element(ctx) {
	let svelte_element;
	let svelte_element_levels = [/*attrs*/ ctx[12]];
	let svelte_element_data = {};

	for (let i = 0; i < svelte_element_levels.length; i += 1) {
		svelte_element_data = assign(svelte_element_data, svelte_element_levels[i]);
	}

	return {
		c() {
			svelte_element = svg_element(/*tag*/ ctx[11]);
			this.h();
		},
		l(nodes) {
			svelte_element = claim_svg_element(nodes, /*tag*/ ctx[11], {});
			children(svelte_element).forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svelte_element, svelte_element_data);
		},
		m(target, anchor) {
			insert_hydration(target, svelte_element, anchor);
		},
		p(ctx, dirty) {
			set_svg_attributes(svelte_element, svelte_element_data = get_spread_update(svelte_element_levels, [dirty & /*iconNode*/ 32 && /*attrs*/ ctx[12]]));
		},
		d(detaching) {
			if (detaching) detach(svelte_element);
		}
	};
}

// (34:2) {#each iconNode as [tag, attrs]}
function create_each_block$1(ctx) {
	let previous_tag = /*tag*/ ctx[11];
	let svelte_element_anchor;
	let svelte_element = /*tag*/ ctx[11] && create_dynamic_element(ctx);

	return {
		c() {
			if (svelte_element) svelte_element.c();
			svelte_element_anchor = empty();
		},
		l(nodes) {
			if (svelte_element) svelte_element.l(nodes);
			svelte_element_anchor = empty();
		},
		m(target, anchor) {
			if (svelte_element) svelte_element.m(target, anchor);
			insert_hydration(target, svelte_element_anchor, anchor);
		},
		p(ctx, dirty) {
			if (/*tag*/ ctx[11]) {
				if (!previous_tag) {
					svelte_element = create_dynamic_element(ctx);
					previous_tag = /*tag*/ ctx[11];
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else if (safe_not_equal(previous_tag, /*tag*/ ctx[11])) {
					svelte_element.d(1);
					svelte_element = create_dynamic_element(ctx);
					previous_tag = /*tag*/ ctx[11];
					svelte_element.c();
					svelte_element.m(svelte_element_anchor.parentNode, svelte_element_anchor);
				} else {
					svelte_element.p(ctx, dirty);
				}
			} else if (previous_tag) {
				svelte_element.d(1);
				svelte_element = null;
				previous_tag = /*tag*/ ctx[11];
			}
		},
		d(detaching) {
			if (detaching) detach(svelte_element_anchor);
			if (svelte_element) svelte_element.d(detaching);
		}
	};
}

function create_fragment$9(ctx) {
	let svg;
	let each_1_anchor;
	let svg_stroke_width_value;
	let svg_class_value;
	let current;
	let each_value = /*iconNode*/ ctx[5];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const default_slot_template = /*#slots*/ ctx[10].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[9], null);

	let svg_levels = [
		defaultAttributes,
		/*$$restProps*/ ctx[7],
		{ width: /*size*/ ctx[2] },
		{ height: /*size*/ ctx[2] },
		{ stroke: /*color*/ ctx[1] },
		{
			"stroke-width": svg_stroke_width_value = /*absoluteStrokeWidth*/ ctx[4]
			? Number(/*strokeWidth*/ ctx[3]) * 24 / Number(/*size*/ ctx[2])
			: /*strokeWidth*/ ctx[3]
		},
		{
			class: svg_class_value = /*mergeClasses*/ ctx[6]('lucide-icon', 'lucide', /*name*/ ctx[0] ? `lucide-${/*name*/ ctx[0]}` : '', /*$$props*/ ctx[8].class)
		}
	];

	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			each_1_anchor = empty();
			if (default_slot) default_slot.c();
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {
				width: true,
				height: true,
				stroke: true,
				"stroke-width": true,
				class: true
			});

			var svg_nodes = children(svg);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(svg_nodes);
			}

			each_1_anchor = empty();
			if (default_slot) default_slot.l(svg_nodes);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(svg, null);
				}
			}

			append_hydration(svg, each_1_anchor);

			if (default_slot) {
				default_slot.m(svg, null);
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (dirty & /*iconNode*/ 32) {
				each_value = /*iconNode*/ ctx[5];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(svg, each_1_anchor);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 512)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[9],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[9])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[9], dirty, null),
						null
					);
				}
			}

			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [
				defaultAttributes,
				dirty & /*$$restProps*/ 128 && /*$$restProps*/ ctx[7],
				(!current || dirty & /*size*/ 4) && { width: /*size*/ ctx[2] },
				(!current || dirty & /*size*/ 4) && { height: /*size*/ ctx[2] },
				(!current || dirty & /*color*/ 2) && { stroke: /*color*/ ctx[1] },
				(!current || dirty & /*absoluteStrokeWidth, strokeWidth, size*/ 28 && svg_stroke_width_value !== (svg_stroke_width_value = /*absoluteStrokeWidth*/ ctx[4]
				? Number(/*strokeWidth*/ ctx[3]) * 24 / Number(/*size*/ ctx[2])
				: /*strokeWidth*/ ctx[3])) && { "stroke-width": svg_stroke_width_value },
				(!current || dirty & /*name, $$props*/ 257 && svg_class_value !== (svg_class_value = /*mergeClasses*/ ctx[6]('lucide-icon', 'lucide', /*name*/ ctx[0] ? `lucide-${/*name*/ ctx[0]}` : '', /*$$props*/ ctx[8].class))) && { class: svg_class_value }
			]));
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(svg);
			destroy_each(each_blocks, detaching);
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	const omit_props_names = ["name","color","size","strokeWidth","absoluteStrokeWidth","iconNode"];
	let $$restProps = compute_rest_props($$props, omit_props_names);
	let { $$slots: slots = {}, $$scope } = $$props;
	let { name = undefined } = $$props;
	let { color = 'currentColor' } = $$props;
	let { size = 24 } = $$props;
	let { strokeWidth = 2 } = $$props;
	let { absoluteStrokeWidth = false } = $$props;
	let { iconNode = [] } = $$props;

	const mergeClasses = (...classes) => classes.filter((className, index, array) => {
		return Boolean(className) && array.indexOf(className) === index;
	}).join(' ');

	$$self.$$set = $$new_props => {
		$$invalidate(8, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		$$invalidate(7, $$restProps = compute_rest_props($$props, omit_props_names));
		if ('name' in $$new_props) $$invalidate(0, name = $$new_props.name);
		if ('color' in $$new_props) $$invalidate(1, color = $$new_props.color);
		if ('size' in $$new_props) $$invalidate(2, size = $$new_props.size);
		if ('strokeWidth' in $$new_props) $$invalidate(3, strokeWidth = $$new_props.strokeWidth);
		if ('absoluteStrokeWidth' in $$new_props) $$invalidate(4, absoluteStrokeWidth = $$new_props.absoluteStrokeWidth);
		if ('iconNode' in $$new_props) $$invalidate(5, iconNode = $$new_props.iconNode);
		if ('$$scope' in $$new_props) $$invalidate(9, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);

	return [
		name,
		color,
		size,
		strokeWidth,
		absoluteStrokeWidth,
		iconNode,
		mergeClasses,
		$$restProps,
		$$props,
		$$scope,
		slots
	];
}

let Component$9 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			name: 0,
			color: 1,
			size: 2,
			strokeWidth: 3,
			absoluteStrokeWidth: 4,
			iconNode: 5
		});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$7(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$8(ctx) {
	let icon;
	let current;

	const icon_spread_levels = [
		{ name: "ellipsis-vertical" },
		/*$$props*/ ctx[1],
		{ iconNode: /*iconNode*/ ctx[0] }
	];

	let icon_props = {
		$$slots: { default: [create_default_slot$7] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;

	const iconNode = [
		["circle", { "cx": "12", "cy": "12", "r": "1" }],
		["circle", { "cx": "12", "cy": "5", "r": "1" }],
		["circle", { "cx": "12", "cy": "19", "r": "1" }]
	];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$8 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$8, create_fragment$8, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$6(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$7(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [{ name: "key" }, /*$$props*/ ctx[1], { iconNode: /*iconNode*/ ctx[0] }];

	let icon_props = {
		$$slots: { default: [create_default_slot$6] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;

	const iconNode = [
		[
			"path",
			{
				"d": "m15.5 7.5 2.3 2.3a1 1 0 0 0 1.4 0l2.1-2.1a1 1 0 0 0 0-1.4L19 4"
			}
		],
		["path", { "d": "m21 2-9.6 9.6" }],
		["circle", { "cx": "7.5", "cy": "15.5", "r": "5.5" }]
	];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$7 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, create_fragment$7, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$5(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$6(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [{ name: "pause" }, /*$$props*/ ctx[1], { iconNode: /*iconNode*/ ctx[0] }];

	let icon_props = {
		$$slots: { default: [create_default_slot$5] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;

	const iconNode = [
		[
			"rect",
			{
				"x": "14",
				"y": "4",
				"width": "4",
				"height": "16",
				"rx": "1"
			}
		],
		[
			"rect",
			{
				"x": "6",
				"y": "4",
				"width": "4",
				"height": "16",
				"rx": "1"
			}
		]
	];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$6 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$6, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$4(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$5(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [{ name: "play" }, /*$$props*/ ctx[1], { iconNode: /*iconNode*/ ctx[0] }];

	let icon_props = {
		$$slots: { default: [create_default_slot$4] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;
	const iconNode = [["polygon", { "points": "6 3 20 12 6 21 6 3" }]];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$5 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, create_fragment$5, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$3(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$4(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [{ name: "search" }, /*$$props*/ ctx[1], { iconNode: /*iconNode*/ ctx[0] }];

	let icon_props = {
		$$slots: { default: [create_default_slot$3] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;

	const iconNode = [
		["circle", { "cx": "11", "cy": "11", "r": "8" }],
		["path", { "d": "m21 21-4.3-4.3" }]
	];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$4 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$4, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$2(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$3(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [{ name: "skip-back" }, /*$$props*/ ctx[1], { iconNode: /*iconNode*/ ctx[0] }];

	let icon_props = {
		$$slots: { default: [create_default_slot$2] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;

	const iconNode = [
		["polygon", { "points": "19 20 9 12 19 4 19 20" }],
		[
			"line",
			{
				"x1": "5",
				"x2": "5",
				"y1": "19",
				"y2": "5"
			}
		]
	];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$3 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$3, create_fragment$3, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot$1(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$2(ctx) {
	let icon;
	let current;

	const icon_spread_levels = [
		{ name: "skip-forward" },
		/*$$props*/ ctx[1],
		{ iconNode: /*iconNode*/ ctx[0] }
	];

	let icon_props = {
		$$slots: { default: [create_default_slot$1] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;

	const iconNode = [
		["polygon", { "points": "5 4 15 12 5 20 5 4" }],
		[
			"line",
			{
				"x1": "19",
				"x2": "19",
				"y1": "5",
				"y2": "19"
			}
		]
	];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$2 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$2, create_fragment$2, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function create_default_slot(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[2].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[3], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 8)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[3],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[3])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[3], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

function create_fragment$1(ctx) {
	let icon;
	let current;
	const icon_spread_levels = [{ name: "x" }, /*$$props*/ ctx[1], { iconNode: /*iconNode*/ ctx[0] }];

	let icon_props = {
		$$slots: { default: [create_default_slot] },
		$$scope: { ctx }
	};

	for (let i = 0; i < icon_spread_levels.length; i += 1) {
		icon_props = assign(icon_props, icon_spread_levels[i]);
	}

	icon = new Component$9({ props: icon_props });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			const icon_changes = (dirty & /*$$props, iconNode*/ 3)
			? get_spread_update(icon_spread_levels, [
					icon_spread_levels[0],
					dirty & /*$$props*/ 2 && get_spread_object(/*$$props*/ ctx[1]),
					dirty & /*iconNode*/ 1 && { iconNode: /*iconNode*/ ctx[0] }
				])
			: {};

			if (dirty & /*$$scope*/ 8) {
				icon_changes.$$scope = { dirty, ctx };
			}

			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;
	const iconNode = [["path", { "d": "M18 6 6 18" }], ["path", { "d": "m6 6 12 12" }]];

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
		if ('$$scope' in $$new_props) $$invalidate(3, $$scope = $$new_props.$$scope);
	};

	$$props = exclude_internal_props($$props);
	return [iconNode, $$props, slots, $$scope];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[42] = list[i];
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[45] = list[i];
	return child_ctx;
}

// (497:14) {:else}
function create_else_block_2(ctx) {
	let t;

	return {
		c() {
			t = text("No track selected");
		},
		l(nodes) {
			t = claim_text(nodes, "No track selected");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (495:14) {#if currentVideoId}
function create_if_block_9(ctx) {
	let t_value = (/*searchResults*/ ctx[6].find(/*func*/ ctx[23])?.title || /*playlist*/ ctx[8].find(/*func_1*/ ctx[24])?.title || 'Unknown Track') + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*searchResults, currentVideoId, playlist*/ 832 && t_value !== (t_value = (/*searchResults*/ ctx[6].find(/*func*/ ctx[23])?.title || /*playlist*/ ctx[8].find(/*func_1*/ ctx[24])?.title || 'Unknown Track') + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (504:14) {:else}
function create_else_block_1(ctx) {
	let t;

	return {
		c() {
			t = text("Select a track to play");
		},
		l(nodes) {
			t = claim_text(nodes, "Select a track to play");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (502:14) {#if currentVideoId}
function create_if_block_8(ctx) {
	let t_value = (/*searchResults*/ ctx[6].find(/*func_2*/ ctx[25])?.artist || /*playlist*/ ctx[8].find(/*func_3*/ ctx[26])?.artist || '') + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*searchResults, currentVideoId, playlist*/ 832 && t_value !== (t_value = (/*searchResults*/ ctx[6].find(/*func_2*/ ctx[25])?.artist || /*playlist*/ ctx[8].find(/*func_3*/ ctx[26])?.artist || '') + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (534:12) {:else}
function create_else_block(ctx) {
	let play;
	let current;
	play = new Component$5({});

	return {
		c() {
			create_component(play.$$.fragment);
		},
		l(nodes) {
			claim_component(play.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(play, target, anchor);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(play.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(play.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(play, detaching);
		}
	};
}

// (532:12) {#if isPlaying}
function create_if_block_7(ctx) {
	let pause;
	let current;
	pause = new Component$6({});

	return {
		c() {
			create_component(pause.$$.fragment);
		},
		l(nodes) {
			claim_component(pause.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(pause, target, anchor);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(pause.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(pause.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(pause, detaching);
		}
	};
}

// (548:8) {#if playerError}
function create_if_block_6(ctx) {
	let div;
	let t;

	return {
		c() {
			div = element("div");
			t = text(/*playerError*/ ctx[12]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, /*playerError*/ ctx[12]);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "error-message svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*playerError*/ 4096) set_data(t, /*playerError*/ ctx[12]);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (558:10) {#each playlist as track}
function create_each_block_1(ctx) {
	let button1;
	let span;
	let t0_value = /*track*/ ctx[45].title + "";
	let t0;
	let t1;
	let button0;
	let morevertical;
	let t2;
	let current;
	let mounted;
	let dispose;
	morevertical = new Component$8({ props: { size: 18 } });

	function click_handler_5() {
		return /*click_handler_5*/ ctx[30](/*track*/ ctx[45]);
	}

	return {
		c() {
			button1 = element("button");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			button0 = element("button");
			create_component(morevertical.$$.fragment);
			t2 = space();
			this.h();
		},
		l(nodes) {
			button1 = claim_element(nodes, "BUTTON", { class: true });
			var button1_nodes = children(button1);
			span = claim_element(button1_nodes, "SPAN", {});
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(button1_nodes);
			button0 = claim_element(button1_nodes, "BUTTON", { class: true, "aria-label": true });
			var button0_nodes = children(button0);
			claim_component(morevertical.$$.fragment, button0_nodes);
			button0_nodes.forEach(detach);
			t2 = claim_space(button1_nodes);
			button1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button0, "class", "more-btn svelte-1vrnyiy");
			attr(button0, "aria-label", "More options");
			attr(button1, "class", "playlist-item svelte-1vrnyiy");
			toggle_class(button1, "active", /*currentVideoId*/ ctx[9] === /*track*/ ctx[45].videoId);
		},
		m(target, anchor) {
			insert_hydration(target, button1, anchor);
			append_hydration(button1, span);
			append_hydration(span, t0);
			append_hydration(button1, t1);
			append_hydration(button1, button0);
			mount_component(morevertical, button0, null);
			append_hydration(button1, t2);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button0, "click", stop_propagation(click_handler_4)),
					listen(button1, "click", click_handler_5)
				];

				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if ((!current || dirty[0] & /*playlist*/ 256) && t0_value !== (t0_value = /*track*/ ctx[45].title + "")) set_data(t0, t0_value);

			if (!current || dirty[0] & /*currentVideoId, playlist*/ 768) {
				toggle_class(button1, "active", /*currentVideoId*/ ctx[9] === /*track*/ ctx[45].videoId);
			}
		},
		i(local) {
			if (current) return;
			transition_in(morevertical.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(morevertical.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(button1);
			destroy_component(morevertical);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (582:2) {#if showSearchModal}
function create_if_block_1(ctx) {
	let div2;
	let div1;
	let button0;
	let x;
	let t0;
	let h2;
	let t1;
	let t2;
	let div0;
	let input;
	let t3;
	let button1;
	let t4;
	let t5;
	let current;
	let mounted;
	let dispose;
	x = new Component$1({});

	function select_block_type_3(ctx, dirty) {
		if (/*isSearching*/ ctx[10]) return create_if_block_2;
		if (/*searchResults*/ ctx[6].length > 0) return create_if_block_3;
		if (/*searchResults*/ ctx[6].length === 0 && !/*isSearching*/ ctx[10]) return create_if_block_5;
	}

	let current_block_type = select_block_type_3(ctx);
	let if_block = current_block_type && current_block_type(ctx);

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			button0 = element("button");
			create_component(x.$$.fragment);
			t0 = space();
			h2 = element("h2");
			t1 = text("Search YouTube");
			t2 = space();
			div0 = element("div");
			input = element("input");
			t3 = space();
			button1 = element("button");
			t4 = text("Search");
			t5 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			button0 = claim_element(div1_nodes, "BUTTON", { class: true });
			var button0_nodes = children(button0);
			claim_component(x.$$.fragment, button0_nodes);
			button0_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			h2 = claim_element(div1_nodes, "H2", {});
			var h2_nodes = children(h2);
			t1 = claim_text(h2_nodes, "Search YouTube");
			h2_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			input = claim_element(div0_nodes, "INPUT", {
				type: true,
				placeholder: true,
				class: true
			});

			t3 = claim_space(div0_nodes);
			button1 = claim_element(div0_nodes, "BUTTON", { class: true });
			var button1_nodes = children(button1);
			t4 = claim_text(button1_nodes, "Search");
			button1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button0, "class", "modal-close svelte-1vrnyiy");
			attr(input, "type", "text");
			attr(input, "placeholder", "Search for tracks...");
			attr(input, "class", "svelte-1vrnyiy");
			attr(button1, "class", "svelte-1vrnyiy");
			attr(div0, "class", "search-input svelte-1vrnyiy");
			attr(div1, "class", "modal-content svelte-1vrnyiy");
			attr(div2, "class", "modal svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, button0);
			mount_component(x, button0, null);
			append_hydration(div1, t0);
			append_hydration(div1, h2);
			append_hydration(h2, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			append_hydration(div0, input);
			set_input_value(input, /*searchQuery*/ ctx[3]);
			append_hydration(div0, t3);
			append_hydration(div0, button1);
			append_hydration(button1, t4);
			append_hydration(div1, t5);
			if (if_block) if_block.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*click_handler_6*/ ctx[31]),
					listen(input, "input", /*input_input_handler*/ ctx[32]),
					listen(input, "keydown", /*keydown_handler_3*/ ctx[33]),
					listen(button1, "click", /*searchYouTube*/ ctx[13])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty[0] & /*searchQuery*/ 8 && input.value !== /*searchQuery*/ ctx[3]) {
				set_input_value(input, /*searchQuery*/ ctx[3]);
			}

			if (current_block_type === (current_block_type = select_block_type_3(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if (if_block) if_block.d(1);
				if_block = current_block_type && current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(div1, null);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(x.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(x.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_component(x);

			if (if_block) {
				if_block.d();
			}

			mounted = false;
			run_all(dispose);
		}
	};
}

// (615:61) 
function create_if_block_5(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("No results found");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "No results found");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (600:43) 
function create_if_block_3(ctx) {
	let div;
	let t;
	let if_block_anchor;
	let each_value = /*searchResults*/ ctx[6].slice(0, /*displayedResults*/ ctx[7]);
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	let if_block = /*searchResults*/ ctx[6].length > /*displayedResults*/ ctx[7] && create_if_block_4(ctx);

	return {
		c() {
			div = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			if (if_block) if_block.c();
			if_block_anchor = empty();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div_nodes);
			}

			div_nodes.forEach(detach);
			t = claim_space(nodes);
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
			this.h();
		},
		h() {
			attr(div, "class", "search-results svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div, null);
				}
			}

			insert_hydration(target, t, anchor);
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty[0] & /*addToPlaylist, searchResults, displayedResults, playVideo*/ 98496) {
				each_value = /*searchResults*/ ctx[6].slice(0, /*displayedResults*/ ctx[7]);
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (/*searchResults*/ ctx[6].length > /*displayedResults*/ ctx[7]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_4(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_each(each_blocks, detaching);
			if (detaching) detach(t);
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (598:8) {#if isSearching}
function create_if_block_2(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("Searching...");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Searching...");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (602:12) {#each searchResults.slice(0, displayedResults) as result}
function create_each_block(ctx) {
	let button;
	let span0;
	let t0_value = /*result*/ ctx[42].title + "";
	let t0;
	let t1;
	let span1;
	let t2_value = /*result*/ ctx[42].artist + "";
	let t2;
	let t3;
	let mounted;
	let dispose;

	function click_handler_7() {
		return /*click_handler_7*/ ctx[34](/*result*/ ctx[42]);
	}

	return {
		c() {
			button = element("button");
			span0 = element("span");
			t0 = text(t0_value);
			t1 = space();
			span1 = element("span");
			t2 = text(t2_value);
			t3 = space();
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			span0 = claim_element(button_nodes, "SPAN", {});
			var span0_nodes = children(span0);
			t0 = claim_text(span0_nodes, t0_value);
			span0_nodes.forEach(detach);
			t1 = claim_space(button_nodes);
			span1 = claim_element(button_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			t2 = claim_text(span1_nodes, t2_value);
			span1_nodes.forEach(detach);
			t3 = claim_space(button_nodes);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span1, "class", "artist svelte-1vrnyiy");
			attr(button, "class", "search-result-item svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			append_hydration(button, span0);
			append_hydration(span0, t0);
			append_hydration(button, t1);
			append_hydration(button, span1);
			append_hydration(span1, t2);
			append_hydration(button, t3);

			if (!mounted) {
				dispose = listen(button, "click", click_handler_7);
				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty[0] & /*searchResults, displayedResults*/ 192 && t0_value !== (t0_value = /*result*/ ctx[42].title + "")) set_data(t0, t0_value);
			if (dirty[0] & /*searchResults, displayedResults*/ 192 && t2_value !== (t2_value = /*result*/ ctx[42].artist + "")) set_data(t2, t2_value);
		},
		d(detaching) {
			if (detaching) detach(button);
			mounted = false;
			dispose();
		}
	};
}

// (612:10) {#if searchResults.length > displayedResults}
function create_if_block_4(ctx) {
	let button;
	let t;
	let mounted;
	let dispose;

	return {
		c() {
			button = element("button");
			t = text("Load More");
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			t = claim_text(button_nodes, "Load More");
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "class", "load-more svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			append_hydration(button, t);

			if (!mounted) {
				dispose = listen(button, "click", /*loadMore*/ ctx[14]);
				mounted = true;
			}
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(button);
			mounted = false;
			dispose();
		}
	};
}

// (623:2) {#if showApiKeyModal}
function create_if_block(ctx) {
	let div2;
	let div1;
	let h2;
	let t0;
	let t1;
	let div0;
	let input;
	let t2;
	let button;
	let t3;
	let mounted;
	let dispose;

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			h2 = element("h2");
			t0 = text("YouTube API Key");
			t1 = space();
			div0 = element("div");
			input = element("input");
			t2 = space();
			button = element("button");
			t3 = text("Save");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h2 = claim_element(div1_nodes, "H2", {});
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, "YouTube API Key");
			h2_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			input = claim_element(div0_nodes, "INPUT", {
				type: true,
				placeholder: true,
				class: true
			});

			t2 = claim_space(div0_nodes);
			button = claim_element(div0_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			t3 = claim_text(button_nodes, "Save");
			button_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(input, "type", "text");
			attr(input, "placeholder", "Enter your API key");
			attr(input, "class", "svelte-1vrnyiy");
			attr(button, "class", "svelte-1vrnyiy");
			attr(div0, "class", "api-key-input svelte-1vrnyiy");
			attr(div1, "class", "modal-content svelte-1vrnyiy");
			attr(div2, "class", "modal svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, h2);
			append_hydration(h2, t0);
			append_hydration(div1, t1);
			append_hydration(div1, div0);
			append_hydration(div0, input);
			set_input_value(input, /*youtubeApiKey*/ ctx[11]);
			append_hydration(div0, t2);
			append_hydration(div0, button);
			append_hydration(button, t3);

			if (!mounted) {
				dispose = [
					listen(input, "input", /*input_input_handler_1*/ ctx[35]),
					listen(button, "click", /*setApiKey*/ ctx[18])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty[0] & /*youtubeApiKey*/ 2048 && input.value !== /*youtubeApiKey*/ ctx[11]) {
				set_input_value(input, /*youtubeApiKey*/ ctx[11]);
			}
		},
		d(detaching) {
			if (detaching) detach(div2);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment(ctx) {
	let div13;
	let div12;
	let header;
	let div0;
	let button0;
	let search;
	let t0;
	let h1;
	let t1;
	let t2;
	let button1;
	let key;
	let t3;
	let button2;
	let x;
	let t4;
	let div10;
	let div7;
	let div2;
	let div1;
	let h20;
	let t5;
	let p;
	let t6;
	let div5;
	let div4;
	let div3;
	let t7;
	let div6;
	let button3;
	let skipback;
	let t8;
	let button4;
	let current_block_type_index;
	let if_block2;
	let button4_aria_label_value;
	let t9;
	let button5;
	let skipforward;
	let t10;
	let t11;
	let div9;
	let h21;
	let t12;
	let t13;
	let div8;
	let t14;
	let div11;
	let t15;
	let t16;
	let current;
	let mounted;
	let dispose;
	search = new Component$4({ props: { size: 20 } });
	key = new Component$7({ props: { size: 20 } });
	x = new Component$1({});

	function select_block_type(ctx, dirty) {
		if (/*currentVideoId*/ ctx[9]) return create_if_block_9;
		return create_else_block_2;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type(ctx);

	function select_block_type_1(ctx, dirty) {
		if (/*currentVideoId*/ ctx[9]) return create_if_block_8;
		return create_else_block_1;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1(ctx);
	skipback = new Component$3({});
	const if_block_creators = [create_if_block_7, create_else_block];
	const if_blocks = [];

	function select_block_type_2(ctx, dirty) {
		if (/*isPlaying*/ ctx[2]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type_2(ctx);
	if_block2 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	skipforward = new Component$2({});
	let if_block3 = /*playerError*/ ctx[12] && create_if_block_6(ctx);
	let each_value_1 = /*playlist*/ ctx[8];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block4 = /*showSearchModal*/ ctx[4] && create_if_block_1(ctx);
	let if_block5 = /*showApiKeyModal*/ ctx[5] && create_if_block(ctx);

	return {
		c() {
			div13 = element("div");
			div12 = element("div");
			header = element("header");
			div0 = element("div");
			button0 = element("button");
			create_component(search.$$.fragment);
			t0 = space();
			h1 = element("h1");
			t1 = text("Music Player");
			t2 = space();
			button1 = element("button");
			create_component(key.$$.fragment);
			t3 = space();
			button2 = element("button");
			create_component(x.$$.fragment);
			t4 = space();
			div10 = element("div");
			div7 = element("div");
			div2 = element("div");
			div1 = element("div");
			h20 = element("h2");
			if_block0.c();
			t5 = space();
			p = element("p");
			if_block1.c();
			t6 = space();
			div5 = element("div");
			div4 = element("div");
			div3 = element("div");
			t7 = space();
			div6 = element("div");
			button3 = element("button");
			create_component(skipback.$$.fragment);
			t8 = space();
			button4 = element("button");
			if_block2.c();
			t9 = space();
			button5 = element("button");
			create_component(skipforward.$$.fragment);
			t10 = space();
			if (if_block3) if_block3.c();
			t11 = space();
			div9 = element("div");
			h21 = element("h2");
			t12 = text("Playlist");
			t13 = space();
			div8 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t14 = space();
			div11 = element("div");
			t15 = space();
			if (if_block4) if_block4.c();
			t16 = space();
			if (if_block5) if_block5.c();
			this.h();
		},
		l(nodes) {
			div13 = claim_element(nodes, "DIV", { class: true });
			var div13_nodes = children(div13);
			div12 = claim_element(div13_nodes, "DIV", { class: true });
			var div12_nodes = children(div12);
			header = claim_element(div12_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			button0 = claim_element(div0_nodes, "BUTTON", { class: true, "aria-label": true });
			var button0_nodes = children(button0);
			claim_component(search.$$.fragment, button0_nodes);
			button0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			h1 = claim_element(div0_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t1 = claim_text(h1_nodes, "Music Player");
			h1_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			button1 = claim_element(div0_nodes, "BUTTON", { class: true, "aria-label": true });
			var button1_nodes = children(button1);
			claim_component(key.$$.fragment, button1_nodes);
			button1_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			button2 = claim_element(header_nodes, "BUTTON", { class: true, "aria-label": true });
			var button2_nodes = children(button2);
			claim_component(x.$$.fragment, button2_nodes);
			button2_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t4 = claim_space(div12_nodes);
			div10 = claim_element(div12_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			div7 = claim_element(div10_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div2 = claim_element(div7_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h20 = claim_element(div1_nodes, "H2", { class: true });
			var h20_nodes = children(h20);
			if_block0.l(h20_nodes);
			h20_nodes.forEach(detach);
			t5 = claim_space(div1_nodes);
			p = claim_element(div1_nodes, "P", { class: true });
			var p_nodes = children(p);
			if_block1.l(p_nodes);
			p_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div7_nodes);
			div5 = claim_element(div7_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true, style: true });
			children(div3).forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			t7 = claim_space(div7_nodes);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			button3 = claim_element(div6_nodes, "BUTTON", { class: true, "aria-label": true });
			var button3_nodes = children(button3);
			claim_component(skipback.$$.fragment, button3_nodes);
			button3_nodes.forEach(detach);
			t8 = claim_space(div6_nodes);
			button4 = claim_element(div6_nodes, "BUTTON", { class: true, "aria-label": true });
			var button4_nodes = children(button4);
			if_block2.l(button4_nodes);
			button4_nodes.forEach(detach);
			t9 = claim_space(div6_nodes);
			button5 = claim_element(div6_nodes, "BUTTON", { class: true, "aria-label": true });
			var button5_nodes = children(button5);
			claim_component(skipforward.$$.fragment, button5_nodes);
			button5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			t10 = claim_space(div7_nodes);
			if (if_block3) if_block3.l(div7_nodes);
			div7_nodes.forEach(detach);
			t11 = claim_space(div10_nodes);
			div9 = claim_element(div10_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			h21 = claim_element(div9_nodes, "H2", { class: true });
			var h21_nodes = children(h21);
			t12 = claim_text(h21_nodes, "Playlist");
			h21_nodes.forEach(detach);
			t13 = claim_space(div9_nodes);
			div8 = claim_element(div9_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div8_nodes);
			}

			div8_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			t14 = claim_space(div12_nodes);
			div11 = claim_element(div12_nodes, "DIV", { id: true });
			children(div11).forEach(detach);
			div12_nodes.forEach(detach);
			t15 = claim_space(div13_nodes);
			if (if_block4) if_block4.l(div13_nodes);
			t16 = claim_space(div13_nodes);
			if (if_block5) if_block5.l(div13_nodes);
			div13_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button0, "class", "icon-btn svelte-1vrnyiy");
			attr(button0, "aria-label", "Search YouTube");
			attr(h1, "class", "svelte-1vrnyiy");
			attr(button1, "class", "icon-btn svelte-1vrnyiy");
			attr(button1, "aria-label", "Set API Key");
			attr(div0, "class", "header-content svelte-1vrnyiy");
			attr(button2, "class", "close-btn svelte-1vrnyiy");
			attr(button2, "aria-label", "Close player");
			attr(header, "class", "player-header svelte-1vrnyiy");
			attr(h20, "class", "track-title svelte-1vrnyiy");
			attr(p, "class", "track-artist svelte-1vrnyiy");
			attr(div1, "class", "track-details svelte-1vrnyiy");
			attr(div2, "class", "track-info svelte-1vrnyiy");
			attr(div3, "class", "progress svelte-1vrnyiy");
			set_style(div3, "width", /*currentTime*/ ctx[0] / /*duration*/ ctx[1] * 100 + "%");
			attr(div4, "class", "progress-bar svelte-1vrnyiy");
			attr(div5, "class", "progress-container svelte-1vrnyiy");
			attr(button3, "class", "control-btn svelte-1vrnyiy");
			attr(button3, "aria-label", "Previous");
			attr(button4, "class", "control-btn play-btn svelte-1vrnyiy");
			attr(button4, "aria-label", button4_aria_label_value = /*isPlaying*/ ctx[2] ? 'Pause' : 'Play');
			attr(button5, "class", "control-btn svelte-1vrnyiy");
			attr(button5, "aria-label", "Next");
			attr(div6, "class", "controls svelte-1vrnyiy");
			attr(div7, "class", "player-main");
			attr(h21, "class", "svelte-1vrnyiy");
			attr(div8, "class", "playlist svelte-1vrnyiy");
			attr(div9, "class", "playlist-section svelte-1vrnyiy");
			attr(div10, "class", "player-content svelte-1vrnyiy");
			attr(div11, "id", "youtube-player");
			attr(div12, "class", "player-card svelte-1vrnyiy");
			attr(div13, "class", "player-container svelte-1vrnyiy");
		},
		m(target, anchor) {
			insert_hydration(target, div13, anchor);
			append_hydration(div13, div12);
			append_hydration(div12, header);
			append_hydration(header, div0);
			append_hydration(div0, button0);
			mount_component(search, button0, null);
			append_hydration(div0, t0);
			append_hydration(div0, h1);
			append_hydration(h1, t1);
			append_hydration(div0, t2);
			append_hydration(div0, button1);
			mount_component(key, button1, null);
			append_hydration(header, t3);
			append_hydration(header, button2);
			mount_component(x, button2, null);
			append_hydration(div12, t4);
			append_hydration(div12, div10);
			append_hydration(div10, div7);
			append_hydration(div7, div2);
			append_hydration(div2, div1);
			append_hydration(div1, h20);
			if_block0.m(h20, null);
			append_hydration(div1, t5);
			append_hydration(div1, p);
			if_block1.m(p, null);
			append_hydration(div7, t6);
			append_hydration(div7, div5);
			append_hydration(div5, div4);
			append_hydration(div4, div3);
			append_hydration(div7, t7);
			append_hydration(div7, div6);
			append_hydration(div6, button3);
			mount_component(skipback, button3, null);
			append_hydration(div6, t8);
			append_hydration(div6, button4);
			if_blocks[current_block_type_index].m(button4, null);
			append_hydration(div6, t9);
			append_hydration(div6, button5);
			mount_component(skipforward, button5, null);
			append_hydration(div7, t10);
			if (if_block3) if_block3.m(div7, null);
			append_hydration(div10, t11);
			append_hydration(div10, div9);
			append_hydration(div9, h21);
			append_hydration(h21, t12);
			append_hydration(div9, t13);
			append_hydration(div9, div8);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div8, null);
				}
			}

			append_hydration(div12, t14);
			append_hydration(div12, div11);
			append_hydration(div13, t15);
			if (if_block4) if_block4.m(div13, null);
			append_hydration(div13, t16);
			if (if_block5) if_block5.m(div13, null);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*click_handler*/ ctx[21]),
					listen(button1, "click", /*click_handler_1*/ ctx[22]),
					listen(button3, "click", click_handler_2),
					listen(button3, "keydown", /*keydown_handler*/ ctx[27]),
					listen(button4, "click", /*togglePlay*/ ctx[17]),
					listen(button4, "keydown", /*keydown_handler_1*/ ctx[28]),
					listen(button5, "click", click_handler_3),
					listen(button5, "keydown", /*keydown_handler_2*/ ctx[29])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if_block0.d(1);
				if_block0 = current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(h20, null);
				}
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if_block1.d(1);
				if_block1 = current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(p, null);
				}
			}

			if (!current || dirty[0] & /*currentTime, duration*/ 3) {
				set_style(div3, "width", /*currentTime*/ ctx[0] / /*duration*/ ctx[1] * 100 + "%");
			}

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type_2(ctx);

			if (current_block_type_index !== previous_block_index) {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block2 = if_blocks[current_block_type_index];

				if (!if_block2) {
					if_block2 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block2.c();
				}

				transition_in(if_block2, 1);
				if_block2.m(button4, null);
			}

			if (!current || dirty[0] & /*isPlaying*/ 4 && button4_aria_label_value !== (button4_aria_label_value = /*isPlaying*/ ctx[2] ? 'Pause' : 'Play')) {
				attr(button4, "aria-label", button4_aria_label_value);
			}

			if (/*playerError*/ ctx[12]) {
				if (if_block3) {
					if_block3.p(ctx, dirty);
				} else {
					if_block3 = create_if_block_6(ctx);
					if_block3.c();
					if_block3.m(div7, null);
				}
			} else if (if_block3) {
				if_block3.d(1);
				if_block3 = null;
			}

			if (dirty[0] & /*currentVideoId, playlist, playVideo*/ 66304) {
				each_value_1 = /*playlist*/ ctx[8];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div8, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*showSearchModal*/ ctx[4]) {
				if (if_block4) {
					if_block4.p(ctx, dirty);

					if (dirty[0] & /*showSearchModal*/ 16) {
						transition_in(if_block4, 1);
					}
				} else {
					if_block4 = create_if_block_1(ctx);
					if_block4.c();
					transition_in(if_block4, 1);
					if_block4.m(div13, t16);
				}
			} else if (if_block4) {
				group_outros();

				transition_out(if_block4, 1, 1, () => {
					if_block4 = null;
				});

				check_outros();
			}

			if (/*showApiKeyModal*/ ctx[5]) {
				if (if_block5) {
					if_block5.p(ctx, dirty);
				} else {
					if_block5 = create_if_block(ctx);
					if_block5.c();
					if_block5.m(div13, null);
				}
			} else if (if_block5) {
				if_block5.d(1);
				if_block5 = null;
			}
		},
		i(local) {
			if (current) return;
			transition_in(search.$$.fragment, local);
			transition_in(key.$$.fragment, local);
			transition_in(x.$$.fragment, local);
			transition_in(skipback.$$.fragment, local);
			transition_in(if_block2);
			transition_in(skipforward.$$.fragment, local);

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(if_block4);
			current = true;
		},
		o(local) {
			transition_out(search.$$.fragment, local);
			transition_out(key.$$.fragment, local);
			transition_out(x.$$.fragment, local);
			transition_out(skipback.$$.fragment, local);
			transition_out(if_block2);
			transition_out(skipforward.$$.fragment, local);
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(if_block4);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div13);
			destroy_component(search);
			destroy_component(key);
			destroy_component(x);
			if_block0.d();
			if_block1.d();
			destroy_component(skipback);
			if_blocks[current_block_type_index].d();
			destroy_component(skipforward);
			if (if_block3) if_block3.d();
			destroy_each(each_blocks, detaching);
			if (if_block4) if_block4.d();
			if (if_block5) if_block5.d();
			mounted = false;
			run_all(dispose);
		}
	};
}
let volume = 50;

function onPlayerReady(event) {
	
} // Player is ready

function handleKeydown(event, action) {
	if (event.key === 'Enter' || event.key === ' ') {
		action();
		event.preventDefault();
	}
}

const click_handler_2 = () => {
	
};

const click_handler_3 = () => {
	
};

const click_handler_4 = () => {
	
};

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let player;
	let currentTime = 0;
	let duration = 0;
	let isPlaying = false;
	let searchQuery = '';
	let showSearchModal = false;
	let showApiKeyModal = false;
	let searchResults = [];
	let displayedResults = 5;
	let playlist = [];
	let currentVideoId = '';
	let isSearching = false;
	let youtubeApiKey = '';
	let playerError = null;

	onMount(() => {
		loadYouTubeAPI();
	});

	function loadYouTubeAPI() {
		const tag = document.createElement('script');
		tag.src = "https://www.youtube.com/iframe_api";
		const firstScriptTag = document.getElementsByTagName('script')[0];
		firstScriptTag.parentNode.insertBefore(tag, firstScriptTag);

		window.onYouTubeIframeAPIReady = () => {
			$$invalidate(20, player = new YT.Player('youtube-player',
			{
					height: '0',
					width: '0',
					videoId: '',
					events: {
						'onReady': onPlayerReady,
						'onStateChange': onPlayerStateChange,
						'onError': onPlayerError
					}
				}));
		};
	}

	function onPlayerStateChange(event) {
		if (event.data == YT.PlayerState.PLAYING) {
			$$invalidate(2, isPlaying = true);
			updateTimeInfo();
		} else if (event.data == YT.PlayerState.PAUSED) {
			$$invalidate(2, isPlaying = false);
		}
	}

	function onPlayerError(event) {
		console.error('YouTube player error:', event.data);
		$$invalidate(12, playerError = `Error: ${event.data}`);
		$$invalidate(2, isPlaying = false);
	}

	function updateTimeInfo() {
		if (player && player.getCurrentTime) {
			$$invalidate(0, currentTime = player.getCurrentTime());
			$$invalidate(1, duration = player.getDuration());

			if (isPlaying) {
				setTimeout(updateTimeInfo, 1000);
			}
		}
	}

	async function searchYouTube() {
		if (!youtubeApiKey) {
			alert("Please enter a YouTube API key first");
			$$invalidate(5, showApiKeyModal = true);
			return;
		}

		if (!searchQuery.trim()) {
			alert("Please enter a search query");
			return;
		}

		$$invalidate(10, isSearching = true);

		try {
			const response = await fetch(`https://www.googleapis.com/youtube/v3/search?part=snippet&q=${encodeURIComponent(searchQuery)}&type=video&key=${youtubeApiKey}&maxResults=25`);

			if (!response.ok) {
				throw new Error(`HTTP error! status: ${response.status}`);
			}

			const data = await response.json();

			$$invalidate(6, searchResults = data.items.map(item => ({
				title: item.snippet.title,
				artist: item.snippet.channelTitle,
				videoId: item.id.videoId
			})));
		} catch(error) {
			console.error('Error fetching YouTube data:', error);
			alert('An error occurred while searching. Please try again.');
			$$invalidate(6, searchResults = []);
		} finally {
			$$invalidate(10, isSearching = false);
		}
	}

	function loadMore() {
		$$invalidate(7, displayedResults += 5);
	}

	function addToPlaylist(track) {
		$$invalidate(8, playlist = [...playlist, track]);
		$$invalidate(4, showSearchModal = false);
	}

	function playVideo(videoId) {
		if (player && player.loadVideoById) {
			$$invalidate(12, playerError = null);

			try {
				player.loadVideoById(videoId);
				$$invalidate(9, currentVideoId = videoId);
				$$invalidate(2, isPlaying = true);
			} catch(error) {
				console.error('Error loading video:', error);
				$$invalidate(12, playerError = `Error loading video: ${error.message}`);
				$$invalidate(2, isPlaying = false);
			}
		}
	}

	function togglePlay() {
		if (player) {
			if (isPlaying) {
				player.pauseVideo();
				$$invalidate(2, isPlaying = false);
			} else {
				if (currentVideoId) {
					player.playVideo();
					$$invalidate(2, isPlaying = true);
				} else if (playlist.length > 0) {
					playVideo(playlist[0].videoId);
				}
			}
		}
	}

	function setApiKey() {
		if (youtubeApiKey.trim()) {
			$$invalidate(5, showApiKeyModal = false);
		} else {
			alert("Please enter a valid API key");
		}
	}

	const click_handler = () => $$invalidate(4, showSearchModal = true);
	const click_handler_1 = () => $$invalidate(5, showApiKeyModal = true);
	const func = r => r.videoId === currentVideoId;
	const func_1 = p => p.videoId === currentVideoId;
	const func_2 = r => r.videoId === currentVideoId;
	const func_3 = p => p.videoId === currentVideoId;

	const keydown_handler = e => handleKeydown(e, () => {
		
	});

	const keydown_handler_1 = e => handleKeydown(e, togglePlay);

	const keydown_handler_2 = e => handleKeydown(e, () => {
		
	});

	const click_handler_5 = track => playVideo(track.videoId);
	const click_handler_6 = () => $$invalidate(4, showSearchModal = false);

	function input_input_handler() {
		searchQuery = this.value;
		$$invalidate(3, searchQuery);
	}

	const keydown_handler_3 = e => e.key === 'Enter' && searchYouTube();

	const click_handler_7 = result => {
		addToPlaylist(result);
		playVideo(result.videoId);
	};

	function input_input_handler_1() {
		youtubeApiKey = this.value;
		$$invalidate(11, youtubeApiKey);
	}

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(19, props = $$props.props);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty[0] & /*player*/ 1048576) {
			if (player && player.setVolume) {
				player.setVolume(volume);
			}
		}
	};

	return [
		currentTime,
		duration,
		isPlaying,
		searchQuery,
		showSearchModal,
		showApiKeyModal,
		searchResults,
		displayedResults,
		playlist,
		currentVideoId,
		isSearching,
		youtubeApiKey,
		playerError,
		searchYouTube,
		loadMore,
		addToPlaylist,
		playVideo,
		togglePlay,
		setApiKey,
		props,
		player,
		click_handler,
		click_handler_1,
		func,
		func_1,
		func_2,
		func_3,
		keydown_handler,
		keydown_handler_1,
		keydown_handler_2,
		click_handler_5,
		click_handler_6,
		input_input_handler,
		keydown_handler_3,
		click_handler_7,
		input_input_handler_1
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 19 }, null, [-1, -1]);
	}
}

export { Component as default };
