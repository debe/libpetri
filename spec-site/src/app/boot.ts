/**
 * Inlined in `<head>` before the CSS paints: applies the stored theme so a viewer who picked
 * one never sees a flash of the other. Keep it tiny; it imports only `theme.ts`.
 */
import { applyThemeChoice, readThemeChoice } from './theme.js';

applyThemeChoice(readThemeChoice());
