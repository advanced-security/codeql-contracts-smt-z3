#define BSLS_PERFORMANCEHINT_PREDICT_UNLIKELY(expr)         (expr)

#define BSLS_ASSERT_ASSERT_IMP(X,LVL) do {                                    \
        if (BSLS_PERFORMANCEHINT_PREDICT_UNLIKELY(!(X))) {                    \
        }                                                                     \
    } while (false)

#define BSLS_ASSERT(X) BSLS_ASSERT_ASSERT_IMP(                     \
                                     X,                                       \
                                     0)

#define BSLS_ASSERT_SAFE(X) BSLS_ASSERT_ASSERT_IMP(                     \
                                     X,                                       \
                                     0)

#define BSLS_ASSERT_OPT(X) BSLS_ASSERT_ASSERT_IMP(                     \
                                     X,                                       \
                                     0)

