import useDefaultProps from './hooks/useDefaultProps';

type Props = {
    prop1: String | undefined;
    prop2: String | undefined;
    prop3: String | undefined;
};

const defaultProps = { prop3: 'Example React default prop' };

export default function Widget2(props: Props) {
    const { prop1, prop2, prop3 } = useDefaultProps(props, defaultProps);
    return <div>{`${prop1} - ${prop2} - ${prop3}`}</div>;
}
