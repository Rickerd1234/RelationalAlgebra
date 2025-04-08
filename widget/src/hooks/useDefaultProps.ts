export default function useDefaultProps<Props extends object>(
    props: Partial<Props>,
    defaults: Partial<Props>
): Partial<Props> {
    return {
        ...defaults,
        ...Object.entries(props).reduce(
            (a: any, [k, v]) => (v == null ? a : ((a[k] = v), a)),
            {}
        ),
    };
}
