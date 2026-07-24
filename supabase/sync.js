module.exports = {
  isEnabled: () => false,
  upsertAgent: () => Promise.resolve(),
  upsertMessage: () => Promise.resolve(),
  upsertChat: () => Promise.resolve(),
  upsertContact: () => Promise.resolve(),
  clearAll: async () => ({ ok: true }),
  flush: () => Promise.resolve(),
};
