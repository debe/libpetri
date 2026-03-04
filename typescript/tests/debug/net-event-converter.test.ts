import { describe, it, expect } from 'vitest';
import { toEventInfo, tokenInfo, compactTokenInfo, convertMarking } from '../../src/debug/net-event-converter.js';
import { tokenOf, unitToken } from '../../src/core/token.js';
import type { NetEvent } from '../../src/event/net-event.js';
import type { TokenInfo } from '../../src/debug/debug-response.js';

const NOW = Date.now();

describe('NetEventConverter', () => {
  describe('toEventInfo', () => {
    it('should convert lifecycle events', () => {
      const started: NetEvent = {
        type: 'execution-started',
        timestamp: NOW,
        netName: 'MyNet',
        executionId: 'exec-1',
      };
      const info = toEventInfo(started);

      expect(info.type).toBe('ExecutionStarted');
      expect(info.transitionName).toBeNull();
      expect(info.placeName).toBeNull();
      expect(info.details['netName']).toBe('MyNet');
      expect(info.details['executionId']).toBe('exec-1');

      const completed: NetEvent = {
        type: 'execution-completed',
        timestamp: NOW,
        netName: 'MyNet',
        executionId: 'exec-1',
        totalDurationMs: 500,
      };
      const completedInfo = toEventInfo(completed);
      expect(completedInfo.type).toBe('ExecutionCompleted');
      expect(completedInfo.details['totalDurationMs']).toBe(500);
    });

    it('should convert transition events', () => {
      const enabled: NetEvent = {
        type: 'transition-enabled',
        timestamp: NOW,
        transitionName: 'T1',
      };
      const info = toEventInfo(enabled);
      expect(info.type).toBe('TransitionEnabled');
      expect(info.transitionName).toBe('T1');
      expect(info.placeName).toBeNull();

      const clockRestarted: NetEvent = {
        type: 'transition-clock-restarted',
        timestamp: NOW,
        transitionName: 'T2',
      };
      expect(toEventInfo(clockRestarted).type).toBe('TransitionClockRestarted');

      const started: NetEvent = {
        type: 'transition-started',
        timestamp: NOW,
        transitionName: 'T1',
        consumedTokens: [tokenOf('val')],
      };
      const startedInfo = toEventInfo(started);
      expect(startedInfo.type).toBe('TransitionStarted');
      expect(Array.isArray(startedInfo.details['consumedTokens'])).toBe(true);

      const tcompleted: NetEvent = {
        type: 'transition-completed',
        timestamp: NOW,
        transitionName: 'T1',
        producedTokens: [tokenOf('out')],
        durationMs: 42,
      };
      const completedInfo = toEventInfo(tcompleted);
      expect(completedInfo.type).toBe('TransitionCompleted');
      expect(completedInfo.details['durationMs']).toBe(42);

      const failed: NetEvent = {
        type: 'transition-failed',
        timestamp: NOW,
        transitionName: 'T1',
        errorMessage: 'boom',
        exceptionType: 'RuntimeException',
      };
      const failedInfo = toEventInfo(failed);
      expect(failedInfo.type).toBe('TransitionFailed');
      expect(failedInfo.details['errorMessage']).toBe('boom');
      expect(failedInfo.details['exceptionType']).toBe('RuntimeException');
    });

    it('should convert timeout events', () => {
      const transTimeout: NetEvent = {
        type: 'transition-timed-out',
        timestamp: NOW,
        transitionName: 'T1',
        deadlineMs: 1000,
        actualDurationMs: 1200,
      };
      const info = toEventInfo(transTimeout);
      expect(info.type).toBe('TransitionTimedOut');
      expect(info.transitionName).toBe('T1');
      expect(info.details['deadlineMs']).toBe(1000);
      expect(info.details['actualDurationMs']).toBe(1200);

      const actionTimeout: NetEvent = {
        type: 'action-timed-out',
        timestamp: NOW,
        transitionName: 'T2',
        timeoutMs: 500,
      };
      const actionInfo = toEventInfo(actionTimeout);
      expect(actionInfo.type).toBe('ActionTimedOut');
      expect(actionInfo.details['timeoutMs']).toBe(500);
    });

    it('should convert token events', () => {
      const token = tokenOf('hello');
      const added: NetEvent = {
        type: 'token-added',
        timestamp: NOW,
        placeName: 'P1',
        token,
      };
      const info = toEventInfo(added);
      expect(info.type).toBe('TokenAdded');
      expect(info.transitionName).toBeNull();
      expect(info.placeName).toBe('P1');
      expect(info.details['token']).toBeDefined();
      expect((info.details['token'] as TokenInfo).type).toBe('string');

      const removed: NetEvent = {
        type: 'token-removed',
        timestamp: NOW,
        placeName: 'P1',
        token,
      };
      const removedInfo = toEventInfo(removed);
      expect(removedInfo.type).toBe('TokenRemoved');
      expect(removedInfo.placeName).toBe('P1');
    });

    it('should convert marking snapshot', () => {
      const token = tokenOf('data');
      const snapshot: NetEvent = {
        type: 'marking-snapshot',
        timestamp: NOW,
        marking: new Map([['P1', [token]]]),
      };
      const info = toEventInfo(snapshot);

      expect(info.type).toBe('MarkingSnapshot');
      expect(info.transitionName).toBeNull();
      expect(info.placeName).toBeNull();
      expect(info.details['marking']).toBeDefined();
    });

    it('should convert log message with and without throwable', () => {
      const withoutThrowable: NetEvent = {
        type: 'log-message',
        timestamp: NOW,
        transitionName: 'T1',
        logger: 'com.example.Foo',
        level: 'INFO',
        message: 'hello',
        error: null,
        errorMessage: null,
      };
      const info = toEventInfo(withoutThrowable);
      expect(info.type).toBe('LogMessage');
      expect(info.transitionName).toBe('T1');
      expect(info.details['message']).toBe('hello');
      expect(info.details['level']).toBe('INFO');
      expect(info.details['throwable']).toBeUndefined();
      expect(info.details['throwableMessage']).toBeUndefined();

      const withThrowable: NetEvent = {
        type: 'log-message',
        timestamp: NOW,
        transitionName: 'T1',
        logger: 'com.example.Foo',
        level: 'ERROR',
        message: 'oops',
        error: 'RuntimeException',
        errorMessage: 'boom',
      };
      const throwInfo = toEventInfo(withThrowable);
      expect(throwInfo.details['throwable']).toBe('RuntimeException');
      expect(throwInfo.details['throwableMessage']).toBe('boom');
    });
  });

  describe('compact mode', () => {
    it('toEventInfo compact should omit token values', () => {
      const token = tokenOf('hello');
      const added: NetEvent = {
        type: 'token-added',
        timestamp: NOW,
        placeName: 'P1',
        token,
      };
      const info = toEventInfo(added, true);

      expect(info.type).toBe('TokenAdded');
      expect(info.placeName).toBe('P1');
      const tokenDetail = info.details['token'] as TokenInfo;
      expect(tokenDetail.type).toBe('string');
      expect(tokenDetail.value).toBeNull();
    });

    it('convertMarking compact should omit token values', () => {
      const token = tokenOf('data');
      const marking = new Map([['P1', [token]]]);
      const result = convertMarking(marking, true);

      expect(Object.keys(result)).toHaveLength(1);
      const tokens = result['P1']!;
      expect(tokens).toHaveLength(1);
      expect(tokens[0]!.type).toBe('string');
      expect(tokens[0]!.value).toBeNull();
    });

    it('convertMarking full should include token values', () => {
      const token = tokenOf('data');
      const marking = new Map([['P1', [token]]]);
      const result = convertMarking(marking, false);

      const tokens = result['P1']!;
      expect(tokens[0]!.type).toBe('string');
      expect(tokens[0]!.value).toBe('data');
    });
  });

  describe('tokenInfo conversion', () => {
    it('should return full value', () => {
      const longValue = 'x'.repeat(200);
      const token = tokenOf(longValue);
      const info = tokenInfo(token);
      expect(info.type).toBe('string');
      expect(info.value).toBe(longValue);
    });

    it('should handle unit token', () => {
      const unit = unitToken();
      const info = tokenInfo(unit);
      expect(info.type).toBe('null');
      expect(info.value).toBe('null');
    });

    it('compactTokenInfo should return type only', () => {
      const token = tokenOf('hello');
      const info = compactTokenInfo(token);
      expect(info.type).toBe('string');
      expect(info.value).toBeNull();
      expect(info.timestamp).toBeDefined();
    });
  });
});
