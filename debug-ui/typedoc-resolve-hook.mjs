// Resolve hook: force typedoc imports to resolve from debug-ui/node_modules,
// preventing the symlinked libpetri from pulling in typescript/node_modules/typedoc.
export function resolve(specifier, context, next) {
  if (specifier === 'typedoc' || specifier.startsWith('typedoc/')) {
    return next(specifier, { ...context, parentURL: import.meta.url });
  }
  return next(specifier, context);
}
